-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch160
-- name    : Polychromatic418967fa_Branch160
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:17:33.854649+00:00
-- url     : https://prove2.me/theorems/85d8b3d4-30a6-4f07-8bc1-f4340f8802e8
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

def Polychromatic418967fa.branch_160 : allB 160 160 :=
  allB_succ' 2 159 160 (Eq.refl Bool.true) (allA_succ_of_accept 1 159 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  159 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 159 160)) (allB_succ' 3 158 160
  (Eq.refl Bool.true) (allA_of_3_1 3 158 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 157 160 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 157 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 157 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 157 160 (accept_3_3 2 157 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 157 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 157 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 157 160)))) (allB_succ' 5 156 160 (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 156 160 4 1 39 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 156 160 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 156 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 156 160 2 1 78 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 156 160 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 156 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156 160))))) (allB_succ' 6 155 160 (Eq.refl
  Bool.true) (allA_of_3_1 6 155 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 154 160 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 154 160 2 3 77 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 154 160 (accept_3_3 5 154 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 154
  160 2 2 77 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  154 160 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 154 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 154 160 2 1 77 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 154 160 (Polychromatic418967fa.accept_12_1_10_4_1_380 1 154 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 154 160))))))) (allB_succ' 8 153 160 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 153 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 153 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 153 160 (Polychromatic418967fa.accept_12_6_9_4_1_96 6 153 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 153 160 (accept_3_3 5 153 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 160 (Polychromatic418967fa.accept_21_4_6_13_1_7137
  4 153 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 153 160
  (Polychromatic418967fa.accept_21_3_6_13_1_8756 3 153 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 153 160 (accept_3_3 2 153 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  153 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 153 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 153 160)))))))) (allB_succ' 9 152 160 (Eq.refl Bool.true) (allA_of_3_1 9 152 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 151 160 (Eq.refl Bool.true) (allA_succ_of_accept 9 151 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 151 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 151 160 (accept_3_3 8 151 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  151 160 (Polychromatic418967fa.accept_15_7_1_10_1_305 7 151 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 151 160 (Polychromatic418967fa.accept_15_6_1_10_1_1549 6 151 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 151 160 (accept_3_3 5 151 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 151 160 (Polychromatic418967fa.accept_18_4_7_16_1_2307 4 151
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 151 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 151 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 151 160 (accept_3_3 2 151 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  151 160 (Polychromatic418967fa.accept_18_1_7_16_1_1342 1 151 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 151 160)))))))))) (allB_succ' 11 150 160 (Eq.refl Bool.true) (allA_succ_of_gcd 10 150 160 10 1
  15 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 150 160
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 150 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 150 160 2 4 75 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 150 160 (Polychromatic418967fa.accept_22_7_18_6_1_7112 7 150 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 150 160 2 3 75 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 150 160 5 1 30 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 150 160 2 2 75 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 150 160 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 150 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 150 160 2 1 75 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 150 160
  (Polychromatic418967fa.accept_9_1_6_7_1_285 1 150 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 150 160))))))))))) (allB_succ' 12 149 160 (Eq.refl Bool.true) (allA_of_3_1 12 149 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 13 148 160 (Eq.refl Bool.true) (allA_succ_of_gcd 12 148 160 4 3 37 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 148 160 (accept_3_3 11
  148 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 148 160 2 5 74 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 148 160
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 148 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 148 160 4 2 37 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 148 160 (Polychromatic418967fa.accept_14_7_8_6_1_1164 7 148 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 148 160 2 3 74 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 148 160 (accept_3_3 5 148 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 148 160 4 1 37 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 148 160 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 148 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 148 160 2 1 74 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 148 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 148
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 148 160))))))))))))) (allB_succ' 14 147 160
  (Eq.refl Bool.true) (allA_succ_of_accept 13 147 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 147 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 147 160
  (Polychromatic418967fa.accept_22_12_15_6_1_8826 12 147 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 147 160 (accept_3_3 11 147 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 147 160 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 147 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 147 160 (Polychromatic418967fa.accept_15_9_12_10_1_809 9 147
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 147 160 (accept_3_3 8 147 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 7
  147 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 147 160
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 147 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 147 160 (accept_3_3 5 147 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  147 160 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 147 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 147 160 (Polychromatic418967fa.accept_19_3_14_8_1_3272 3 147 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 147 160 (accept_3_3 2 147 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 147 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 147 160)))))))))))))) (allB_succ' 15 146 160
  (Eq.refl Bool.true) (allA_of_3_1 15 146 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 145 160 (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 145 160 5 3 29 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 145 160 (accept_3_3 14 145 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 145 160 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 145 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 145 160 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 145 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 145 160 (accept_3_3 11 145 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 145 160 5 2 29 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 145 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 145 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 145 160 (accept_3_3 8 145 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  145 160 (Polychromatic418967fa.accept_18_7_1_16_1_578 7 145 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 145 160 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 145 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 145 160 5 1 29 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 145 160 (Polychromatic418967fa.accept_7_4_5_6_1_344 4
  145 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 145 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 145 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 145 160 (accept_3_3 2 145 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  145 160 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 145 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 145 160)))))))))))))))) (allB_succ' 17 144 160 (Eq.refl Bool.true) (allA_succ_of_gcd 16 144 160
  16 1 9 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 144
  160 (Polychromatic418967fa.accept_21_15_18_13_1_8747 15 144 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 144 160 2 7 72 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 144 160 (Polychromatic418967fa.accept_25_13_19_10_1_3337 13 144 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 144 160 4 3 36 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 144 160 (accept_3_3 11
  144 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 144 160 2 5 72 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 144 160
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 144 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 144 160 8 1 18 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 144 160 (Polychromatic418967fa.accept_11_7_1_6_1_1281 7 144 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 144 160 2 3 72 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 144 160 (accept_3_3 5 144 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 144 160 4 1 36 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 144 160 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 144 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 144 160 2 1 72 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 144 160 (Polychromatic418967fa.accept_15_1_9_10_1_2327
  1 144 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144 160))))))))))))))))) (allB_succ'
  18 143 160 (Eq.refl Bool.true) (allA_of_3_1 18 143 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 142 160
  (Eq.refl Bool.true) (allA_succ_of_gcd 18 142 160 2 9 71 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 142 160 (accept_3_3 17 142 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 142 160 2 8 71 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 142 160 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 142 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 142 160 2 7 71 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 142 160 (Polychromatic418967fa.accept_12_1_10_4_1_380
  13 142 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 142 160 2 6 71 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 142 160
  (accept_3_3 11 142 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 142 160 2 5 71 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 142 160
  (Polychromatic418967fa.accept_21_9_16_13_1_1541 9 142 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 142 160 2 4 71 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 142 160 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 142 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 142 160 2 3 71 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 142 160 (accept_3_3 5 142 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 142 160 2 2 71 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 142 160 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 142 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 142 160 2 1 71 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 142 160 (Polychromatic418967fa.accept_7_1_2_6_1_55 1
  142 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142 160))))))))))))))))))) (allB_succ'
  20 141 160 (Eq.refl Bool.true) (allA_succ_of_accept 19 141 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 141 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 141 160
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 141 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 141 160 (accept_3_3 17 141 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 141 160 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 141 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 141 160 (Polychromatic418967fa.accept_13_2_11_4_1_445 15 141 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 141 160 (accept_3_3 14 141 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 141 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 141 160
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 141 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 141 160 (accept_3_3 11 141 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 141 160 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 141 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 141 160 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 141 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 141 160 (accept_3_3 8 141 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 141 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 141 160
  (Polychromatic418967fa.accept_12_6_9_4_1_96 6 141 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 141 160 (accept_3_3 5 141 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  141 160 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 141 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 141 160 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 141 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 141 160 (accept_3_3 2 141 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 141 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 141 160)))))))))))))))))))) (allB_succ' 21 140 160
  (Eq.refl Bool.true) (allA_of_3_1 21 140 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 139 160 (Eq.refl
  Bool.true) (allA_succ_of_accept 21 139 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 139 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 139 160 (accept_3_3 20 139 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 139 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 139 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 139 160
  (Polychromatic418967fa.accept_13_5_9_4_1_441 18 139 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 139 160 (accept_3_3 17 139 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 139 160 (Polychromatic418967fa.accept_17_16_3_7_1_5028 16 139 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 139 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 139 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 139 160 (accept_3_3 14 139 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 139 160 (Polychromatic418967fa.accept_15_13_4_10_1_821 13 139 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 139 160
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 139 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 139 160 (accept_3_3 11 139 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 139 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 139 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 139 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 139 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 139 160 (accept_3_3 8 139 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 139 160 (Polychromatic418967fa.accept_13_7_9_4_1_918 7 139 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 139 160
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 139 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 139 160 (accept_3_3 5 139 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  139 160 (Polychromatic418967fa.accept_17_4_3_7_1_4971 4 139 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 139 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 139 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 139 160 (accept_3_3 2 139 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 139 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 139 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 139 160)))))))))))))))))))))) (allB_succ' 23 138 160
  (Eq.refl Bool.true) (allA_succ_of_gcd 22 138 160 2 11 69 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 138 160 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 138 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 138 160 2 10 69 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 138 160
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 138 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 138 160 2 9 69 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 138 160 (accept_3_3 17 138 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  138 160 2 8 69 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 138 160 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 138 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 138 160 2 7 69 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 138 160 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 138 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 138 160 2 6 69 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 138 160 (accept_3_3 11 138 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 138 160 2 5 69 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 138 160
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 138 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 138 160 2 4 69 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 138 160 (Polychromatic418967fa.accept_15_7_3_10_1_817 7 138 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 138 160 2 3 69 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 138 160 (accept_3_3 5 138 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 138 160 2 2 69 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 138 160 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 138 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 138 160 2 1 69 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 138 160 (Polychromatic418967fa.accept_7_1_5_6_1_59 1
  138 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138 160)))))))))))))))))))))))
  (allB_succ' 24 137 160 (Eq.refl Bool.true) (allA_of_3_1 24 137 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 25 136 160 (Eq.refl Bool.true) (allA_succ_of_gcd 24 136 160 8 3 17 20 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 136 160 (accept_3_3 23 136 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 136 160 2 11 68 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 136 160 (Polychromatic418967fa.accept_9_3_1_7_1_97 21
  136 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 136 160 4 5 34 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 136 160
  (Polychromatic418967fa.accept_18_1_10_16_1_566 19 136 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 136 160 2 9 68 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 136 160 (accept_3_3 17 136 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  136 160 8 2 17 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 136 160 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 136 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 136 160 2 7 68 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 136 160 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 136 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 136 160 4 3 34 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 136 160 (accept_3_3 11 136 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 136 160 2 5 68 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 136 160
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 136 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 136 160 8 1 17 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 136 160 (Polychromatic418967fa.accept_13_7_6_4_1_933 7 136 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 136 160 2 3 68 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 136 160 (accept_3_3 5 136 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 136 160 4 1 34 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 136 160 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 136 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 136 160 2 1 68 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 136 160 (Polychromatic418967fa.accept_18_1_10_16_1_566
  1 136 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 136 160)))))))))))))))))))))))))
  (allB_succ' 26 135 160 (Eq.refl Bool.true) (allA_succ_of_gcd 25 135 160 5 5 27 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 135 160
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 135 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 135 160 (accept_3_3 23 135 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 135 160 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 135 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 135 160 (Polychromatic418967fa.accept_22_21_3_6_1_8825 21 135 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 135 160 5 4 27 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 135 160
  (Polychromatic418967fa.accept_6_1_3_4_1_1 19 135 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 135 160 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 135 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 135 160 (accept_3_3 17 135 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 135 160 (Polychromatic418967fa.accept_21_16_9_13_1_4127 16 135 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 135 160 5 3 27 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 135 160 (accept_3_3 14 135 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 13
  135 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 135 160
  (Polychromatic418967fa.accept_13_12_5_4_1_3133 12 135 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 135 160 (accept_3_3 11 135 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  135 160 5 2 27 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 135 160 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 135 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 135 160 (accept_3_3 8 135 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 135 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 135 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 135 160 (Polychromatic418967fa.accept_12_6_3_4_1_394 6 135 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 135 160 5 1 27 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 135 160
  (Polychromatic418967fa.accept_7_4_2_6_1_337 4 135 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 135 160 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 135 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 135 160 (accept_3_3 2 135 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 135 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 135 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135 160)))))))))))))))))))))))))) (allB_succ' 27 134 160 (Eq.refl
  Bool.true) (allA_of_3_1 27 134 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 133 160 (Eq.refl Bool.true)
  (allA_succ_of_accept 27 133 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 133 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 133 160 (accept_3_3 26 133 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 133 160 (Polychromatic418967fa.accept_13_12_3_4_1_928 25 133 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 133 160
  (Polychromatic418967fa.accept_22_2_1_6_1_3903 24 133 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 133 160 (accept_3_3 23 133 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 133 160 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 133 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 133 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 133 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 133 160 (accept_3_3 20 133 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 133 160 (Polychromatic418967fa.accept_15_4_13_10_1_1508 19 133 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 133 160
  (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 133 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 133 160 (accept_3_3 17 133 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 133 160 (Polychromatic418967fa.accept_11_5_1_6_1_774 16 133 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 133 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 133 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 133 160 (accept_3_3 14 133 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 133 160 (Polychromatic418967fa.accept_14_13_7_6_1_3525 13 133 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 133 160
  (Polychromatic418967fa.accept_13_12_3_4_1_928 12 133 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 133 160 (accept_3_3 11 133 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 133 160 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 133 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 133 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 133 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 133 160 (accept_3_3 8 133 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 133 160 (Polychromatic418967fa.accept_11_7_1_6_1_1281 7 133 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 133 160
  (Polychromatic418967fa.accept_17_6_14_7_1_6115 6 133 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 133 160 (accept_3_3 5 133 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  133 160 (Polychromatic418967fa.accept_15_4_13_10_1_1508 4 133 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 133 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 133 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 133 160 (accept_3_3 2 133 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 133 160 (Polychromatic418967fa.accept_13_1_3_4_1_925 1 133 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 133 160)))))))))))))))))))))))))))) (allB_succ' 29 132
  160 (Eq.refl Bool.true) (allA_succ_of_gcd 28 132 160 4 7 33 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 132 160 (Polychromatic418967fa.accept_31_27_8_5_1_8824 27 132
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 132 160 2 13 66 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 132 160
  (Polychromatic418967fa.accept_13_12_2_4_1_3131 25 132 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 132 160 4 6 33 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 132 160 (accept_3_3 23 132 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  132 160 2 11 66 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 132 160 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 132 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 132 160 4 5 33 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 132 160 (Polychromatic418967fa.accept_9_1_6_7_1_285 19
  132 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 132 160 2 9 66 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 132 160 (accept_3_3 17
  132 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 132 160 4 4 33 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 132 160
  (Polychromatic418967fa.accept_18_15_6_16_1_4730 15 132 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 132 160 2 7 66 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 132 160 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 132 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 132 160 4 3 33 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 132 160 (accept_3_3 11 132 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 132 160 2 5 66 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 132 160
  (Polychromatic418967fa.accept_15_9_12_10_1_809 9 132 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 132 160 4 2 33 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 132 160 (Polychromatic418967fa.accept_15_7_12_10_1_4335 7 132 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132 160 2 3 66 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 132 160 (accept_3_3 5 132 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 132 160 4 1 33 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 132 160 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 132 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 132 160 2 1 66 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 132 160 (Polychromatic418967fa.accept_9_1_6_7_1_285 1
  132 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132 160)))))))))))))))))))))))))))))
  (allB_succ' 30 131 160 (Eq.refl Bool.true) (allA_of_3_1 30 131 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 31 130 160 (Eq.refl Bool.true) (allA_succ_of_gcd 30 130 160 10 3 13 16 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 130 160 (accept_3_3 29 130 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 130 160 2 14 65 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 130 160 (Polychromatic418967fa.accept_21_6_4_13_1_8740
  27 130 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 130 160 2 13 65 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 130 160 5 5 26 32
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 130 160 2 12 65
  80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 130 160
  (accept_3_3 23 130 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 130 160 2 11 65 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 130 160
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 130 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 130 160 10 2 13 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 130 160 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 130 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 130 160 2 9 65 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 130 160 (accept_3_3 17 130 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 130 160 2 8 65 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 130 160 5 3 26 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 130 160 2 7 65 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 130 160 (Polychromatic418967fa.accept_12_1_10_4_1_380
  13 130 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 130 160 2 6 65 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 130 160
  (accept_3_3 11 130 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 130 160 10 1 13 16 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 130 160
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 130 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 130 160 2 4 65 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 130 160 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 130 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 130 160 2 3 65 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 130 160 5 1 26 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 130 160 2 2 65 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 130 160 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 130 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 130 160 2 1 65 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 130 160
  (Polychromatic418967fa.accept_9_1_4_7_1_7 1 130 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 130 160))))))))))))))))))))))))))))))) (allB_succ' 32 129 160 (Eq.refl Bool.true) (allA_succ_of_accept 31
  129 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 129 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 129 160 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 129 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 129 160 (accept_3_3 29 129 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 129 160 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 129 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 129 160
  (Polychromatic418967fa.accept_15_12_9_10_1_2326 27 129 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 129 160 (accept_3_3 26 129 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 129 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 129 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 129 160 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 129 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 129 160 (accept_3_3 23 129 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 160 (Polychromatic418967fa.accept_9_4_3_7_1_296
  22 129 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 129 160
  (Polychromatic418967fa.accept_13_8_12_4_1_4858 21 129 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 129 160 (accept_3_3 20 129 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 129 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 129 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 129 160 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 129 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 129 160 (accept_3_3 17 129 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 160 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 129 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 129 160
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 129 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 129 160 (accept_3_3 14 129 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 129 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 129 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 129 160 (Polychromatic418967fa.accept_15_12_9_10_1_2326 12 129 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 129 160 (accept_3_3 11 129 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 160 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 129 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 129 160
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 129 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 129 160 (accept_3_3 8 129 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  129 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 129 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 129 160 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 129 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 129 160 (accept_3_3 5 129 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 160 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 129 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 129 160
  (Polychromatic418967fa.accept_11_3_8_6_1_788 3 129 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 129 160 (accept_3_3 2 129 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  129 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 129 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 129 160)))))))))))))))))))))))))))))))) (allB_succ' 33 128 160 (Eq.refl Bool.true) (allA_of_3_1
  33 128 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 127 160 (Eq.refl Bool.true) (allA_succ_of_accept 33
  127 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 127 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 127 160 (accept_3_3 32 127 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 127 160 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 127 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 127 160 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 127 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 127 160 (accept_3_3 29 127 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 127 160
  (Polychromatic418967fa.accept_18_10_1_16_1_579 28 127 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 127 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 127 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 127 160 (accept_3_3 26 127 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 127 160 (Polychromatic418967fa.accept_18_7_1_16_1_578 25 127 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 127 160
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 127 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 127 160 (accept_3_3 23 127 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 127 160 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 127 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 127 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 127 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 127 160 (accept_3_3 20 127 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 127 160 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 127 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 127 160
  (Polychromatic418967fa.accept_13_5_10_4_1_1564 18 127 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 127 160 (accept_3_3 17 127 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 127 160 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 127 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 127 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 127 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 127 160 (accept_3_3 14 127 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 127 160 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 127 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 127 160
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 127 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 127 160 (accept_3_3 11 127 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 127 160 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 127 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 127 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 127 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 127 160 (accept_3_3 8 127 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 127 160 (Polychromatic418967fa.accept_13_7_10_4_1_919 7 127 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 127 160
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 127 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 127 160 (accept_3_3 5 127 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  127 160 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 127 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 127 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 127 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 127 160 (accept_3_3 2 127 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 127 160 (Polychromatic418967fa.accept_13_1_10_4_1_954 1 127 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 127 160)))))))))))))))))))))))))))))))))) (allB_succ' 35
  126 160 (Eq.refl Bool.true) (allA_succ_of_gcd 34 126 160 2 17 63 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 126 160 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 126 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 126 160 2 16 63 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 126 160
  (Polychromatic418967fa.accept_13_5_9_4_1_441 31 126 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 126 160 2 15 63 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 126 160 (accept_3_3 29 126 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 126 160 2 14 63 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 126 160 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 126 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 126 160 2 13 63 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 126 160
  (Polychromatic418967fa.accept_19_6_12_8_1_8798 25 126 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 126 160 2 12 63 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 126 160 (accept_3_3 23 126 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 126 160 2 11 63 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 126 160 (Polychromatic418967fa.accept_11_10_5_6_1_1842 21 126 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 126 160 2 10 63 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 126 160
  (Polychromatic418967fa.accept_13_6_9_4_1_2288 19 126 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 126 160 2 9 63 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 126 160 (accept_3_3 17 126 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  126 160 2 8 63 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 126 160 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 126 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 126 160 2 7 63 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 126 160 (Polychromatic418967fa.accept_22_13_16_6_1_8823 13 126 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 126 160 2 6 63 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 126 160 (accept_3_3 11
  126 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 126 160 2 5 63 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 126 160
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 126 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 126 160 2 4 63 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 126 160 (Polychromatic418967fa.accept_13_7_9_4_1_918 7 126 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 126 160 2 3 63 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 126 160 (accept_3_3 5 126 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 126 160 2 2 63 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 126 160 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 126 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 126 160 2 1 63 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 126 160 (Polychromatic418967fa.accept_11_1_5_6_1_397 1
  126 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  160))))))))))))))))))))))))))))))))))) (allB_succ' 36 125 160 (Eq.refl Bool.true) (allA_of_3_1 36 125 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 124 160 (Eq.refl Bool.true) (allA_succ_of_gcd 36 124 160 4 9 31 40
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 124 160
  (accept_3_3 35 124 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 124 160 2 17 62 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 124 160
  (Polychromatic418967fa.accept_23_10_9_22_1_8822 33 124 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 124 160 4 8 31 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 124 160 (Polychromatic418967fa.accept_11_9_3_6_1_797 31 124 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 124 160 2 15 62 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 124 160 (accept_3_3 29 124 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 124 160 4 7 31 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 124 160
  (Polychromatic418967fa.accept_14_13_12_6_1_2735 27 124 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 124 160 2 13 62 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 124 160 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 124 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 124 160 4 6 31 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 124 160 (accept_3_3 23 124 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 124 160 2 11 62 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 124 160
  (Polychromatic418967fa.accept_15_6_4_10_1_2319 21 124 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 124 160 4 5 31 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 124 160 (Polychromatic418967fa.accept_11_8_3_6_1_1855 19 124 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 124 160 2 9 62 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 124 160 (accept_3_3 17 124 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 124 160 4 4 31 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 124 160 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 124 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 124 160 2 7 62 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 124 160
  (Polychromatic418967fa.accept_14_13_12_6_1_2735 13 124 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 124 160 4 3 31 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 124 160 (accept_3_3 11 124 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 124 160 2 5 62 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 124 160 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 124 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 124 160 4 2 31 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 124 160 (Polychromatic418967fa.accept_15_7_4_10_1_1513 7 124 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 124 160 2 3 62 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 124 160 (accept_3_3 5 124 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 124 160 4 1 31 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 124 160 (Polychromatic418967fa.accept_13_3_7_4_1_435 3
  124 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 124 160 2 1 62 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 124 160
  (Polychromatic418967fa.accept_7_1_5_6_1_59 1 124 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 124 160))))))))))))))))))))))))))))))))))))) (allB_succ' 38 123 160 (Eq.refl Bool.true) (allA_succ_of_accept
  37 123 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 123 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 123 160 (Polychromatic418967fa.accept_13_10_6_4_1_1583 36 123 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 123 160 (accept_3_3 35 123 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 123 160 (Polychromatic418967fa.accept_23_11_8_22_1_8821 34 123
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 123 160
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 123 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 123 160 (accept_3_3 32 123 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 123 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 123 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 123 160 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 123 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 123 160 (accept_3_3 29 123 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 123 160 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 123 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 123 160
  (Polychromatic418967fa.accept_18_9_15_16_1_8759 27 123 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 123 160 (accept_3_3 26 123 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 123 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 123 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 123 160 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 123 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 123 160 (accept_3_3 23 123 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 123 160 (Polychromatic418967fa.accept_9_4_6_7_1_286
  22 123 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 123 160
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 123 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 123 160 (accept_3_3 20 123 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 123 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 123 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 123 160 (Polychromatic418967fa.accept_12_6_3_4_1_394 18 123 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 123 160 (accept_3_3 17 123 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 123 160 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 123 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 123 160
  (Polychromatic418967fa.accept_11_4_2_6_1_389 15 123 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 123 160 (accept_3_3 14 123 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 123 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 123 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 123 160 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 123 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 123 160 (accept_3_3 11 123 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 123 160 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 123 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 123 160
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 123 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 123 160 (accept_3_3 8 123 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  123 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 123 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 123 160 (Polychromatic418967fa.accept_12_6_3_4_1_394 6 123 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 123 160 (accept_3_3 5 123 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 160 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 123 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 123 160
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 123 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 123 160 (accept_3_3 2 123 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  123 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 123 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 123 160)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 122 160 (Eq.refl Bool.true)
  (allA_of_3_1 39 122 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 40 121 160 (Eq.refl Bool.true)
  (allA_succ_of_accept 39 121 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 121 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 121 160 (accept_3_3 38 121 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 121 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 121 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 121 160 (Polychromatic418967fa.accept_7_1_2_6_1_55 36
  121 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 121 160 (accept_3_3 35
  121 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 121 160
  (Polychromatic418967fa.accept_12_10_1_4_1_392 34 121 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 121 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 121 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 121 160 (accept_3_3 32 121 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 121 160 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 121 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 121 160 (Polychromatic418967fa.accept_9_3_4_7_1_89 30
  121 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 121 160 (accept_3_3 29
  121 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 121 160
  (Polychromatic418967fa.accept_9_1_4_7_1_7 28 121 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 121 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 121 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 121 160 (accept_3_3 26 121 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 121 160 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 121 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 121 160 (Polychromatic418967fa.accept_7_3_2_6_1_56 24
  121 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 121 160 (accept_3_3 23
  121 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 121 160
  (Polychromatic418967fa.accept_7_1_2_6_1_55 22 121 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 121 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 121 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 121 160 (accept_3_3 20 121 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 121 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 121 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 121 160 (Polychromatic418967fa.accept_7_4_2_6_1_337
  18 121 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 121 160 (accept_3_3 17
  121 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 121 160
  (Polychromatic418967fa.accept_19_16_7_8_1_8820 16 121 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 121 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 121 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 121 160 (accept_3_3 14 121 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 121 160 (Polychromatic418967fa.accept_15_13_1_10_1_816 13 121 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 121 160
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 121 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 121 160 (accept_3_3 11 121 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 121 160 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 121 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 121 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 121 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 121 160 (accept_3_3 8 121 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 121 160 (Polychromatic418967fa.accept_15_7_1_10_1_305 7 121 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 121 160
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 121 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 121 160 (accept_3_3 5 121 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  121 160 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 121 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 121 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 121 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 121 160 (accept_3_3 2 121 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 121 160 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 121 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 121 160))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 41 120 160 (Eq.refl Bool.true) (allA_succ_of_gcd 40 120 160 40 1 3 4 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 120 160
  (Polychromatic418967fa.accept_21_18_15_13_1_4130 39 120 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 120 160 2 19 60 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 120 160 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 120 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 120 160 4 9 30 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 120 160 5 7 24 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 120 160 2 17 60 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 120 160
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 120 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 120 160 8 4 15 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 120 160 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 120 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 120 160 10 3 12 16 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 120 160 (accept_3_3 29 120 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 120 160 4 7 30 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 120 160 (Polychromatic418967fa.accept_11_5_10_6_1_793 27 120
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 120 160 2 13 60 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 120 160 5 5 24 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 120 160 8 3 15 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 120 160 (accept_3_3 23
  120 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 120 160 2 11 60 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 120 160
  (Polychromatic418967fa.accept_14_7_8_6_1_1164 21 120 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 120 160 20 1 6 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 120 160 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 120 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 120 160 2 9 60 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 120 160 (accept_3_3 17 120 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 120 160 8 2 15 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 120 160 5 3 24 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 120 160 2 7 60 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 120 160 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 120 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 160 4 3 30 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 160 (accept_3_3 11
  120 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 120 160 10 1 12 16 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 120 160
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 120 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 120 160 8 1 15 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 120 160 (Polychromatic418967fa.accept_13_7_3_4_1_459 7 120 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120 160 2 3 60 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 120 160 5 1 24 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 120 160 4 1 30 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 120 160 (Polychromatic418967fa.accept_19_3_6_8_1_8819 3 120 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 120 160 2 1 60 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 120 160
  (Polychromatic418967fa.accept_9_1_3_7_1_6 1 120 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 120 160))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 119 160 (Eq.refl Bool.true) (allA_of_3_1 42
  119 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 118 160 (Eq.refl Bool.true) (allA_succ_of_gcd 42 118
  160 2 21 59 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  118 160 (accept_3_3 41 118 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 118 160 2 20 59 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 118 160
  (Polychromatic418967fa.accept_9_3_1_7_1_97 39 118 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 118 160 2 19 59 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 118 160 (Polychromatic418967fa.accept_12_1_10_4_1_380 37 118 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 118 160 2 18 59 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 118 160 (accept_3_3 35 118 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 118 160 2 17 59 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 118 160
  (Polychromatic418967fa.accept_9_6_1_7_1_577 33 118 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 118 160 2 16 59 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 118 160 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 118 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 118 160 2 15 59 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 118 160 (accept_3_3 29 118 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 118 160 2 14 59 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 118 160
  (Polychromatic418967fa.accept_15_12_13_10_1_812 27 118 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 118 160 2 13 59 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 118 160 (Polychromatic418967fa.accept_11_3_8_6_1_788 25 118 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 118 160 2 12 59 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 118 160 (accept_3_3 23 118 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 118 160 2 11 59 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 118 160
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 118 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 118 160 2 10 59 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 118 160 (Polychromatic418967fa.accept_12_7_10_4_1_382 19 118 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 118 160 2 9 59 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 118 160 (accept_3_3 17 118 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 118 160 2 8 59 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 118 160
  (Polychromatic418967fa.accept_9_6_1_7_1_577 15 118 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 118 160 2 7 59 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 118 160 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 118 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 118 160 2 6 59 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 118 160 (accept_3_3 11 118 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 118 160 2 5 59 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 118 160 (Polychromatic418967fa.accept_19_9_4_8_1_8805 9 118 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 118 160 2 4 59 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 118 160
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 118 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 118 160 2 3 59 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 118 160 (accept_3_3 5 118 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 118
  160 2 2 59 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  118 160 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 118 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 118 160 2 1 59 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 118 160 (Polychromatic418967fa.accept_12_1_10_4_1_380 1 118 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118 160))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44
  117 160 (Eq.refl Bool.true) (allA_succ_of_accept 43 117 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 117 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 117 160
  (Polychromatic418967fa.accept_12_6_9_4_1_96 42 117 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 117 160 (accept_3_3 41 117 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 117 160 (Polychromatic418967fa.accept_22_18_7_6_1_7109 40 117 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 117 160 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 117 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 117 160 (accept_3_3 38 117 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 117 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 117 160
  (Polychromatic418967fa.accept_7_1_5_6_1_59 36 117 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 117 160 (accept_3_3 35 117 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 117 160 (Polychromatic418967fa.accept_11_1_7_6_1_378 34 117 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 117 160 (Polychromatic418967fa.accept_18_15_9_16_1_6029 33 117 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 117 160 (accept_3_3 32 117 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 117 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 117 160
  (Polychromatic418967fa.accept_12_6_9_4_1_96 30 117 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 117 160 (accept_3_3 29 117 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 117 160 (Polychromatic418967fa.accept_15_13_12_10_1_4352 28 117 160 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 117 160 (Polychromatic418967fa.accept_14_13_5_6_1_2747 27 117 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 117 160 (accept_3_3 26 117 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 25
  117 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 117 160
  (Polychromatic418967fa.accept_15_9_12_10_1_809 24 117 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 117 160 (accept_3_3 23 117 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 117 160 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 117 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 117 160 (Polychromatic418967fa.accept_15_6_12_10_1_1543 21 117 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 117 160 (accept_3_3 20 117 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 117 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 117 160
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 117 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 117 160 (accept_3_3 17 117 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 117 160 (Polychromatic418967fa.accept_26_16_13_4_1_8818 16 117 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 117 160 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 117 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 160 (accept_3_3 14 117 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 117 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 117 160
  (Polychromatic418967fa.accept_11_1_7_6_1_378 12 117 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 117 160 (accept_3_3 11 117 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 117 160 (Polychromatic418967fa.accept_26_10_13_4_1_8817 10 117 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 117 160 (Polychromatic418967fa.accept_15_9_12_10_1_809 9 117 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 160 (accept_3_3 8 117 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 117 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 160
  (Polychromatic418967fa.accept_12_6_9_4_1_96 6 117 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 117 160 (accept_3_3 5 117 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  117 160 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 117 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 117 160 (Polychromatic418967fa.accept_21_3_12_13_1_8816 3 117 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 160 (accept_3_3 2 117 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 117 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  160)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 116 160 (Eq.refl Bool.true) (allA_of_3_1 45 116 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 46 115 160 (Eq.refl Bool.true) (allA_succ_of_gcd 45 115 160 5 9
  23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 115 160
  (accept_3_3 44 115 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 115 160
  (Polychromatic418967fa.accept_11_10_5_6_1_1842 43 115 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 115 160 (Polychromatic418967fa.accept_24_18_19_16_1_5217 42 115 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 115 160 (accept_3_3 41 115 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 115 160 5 8 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 115 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 115 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 115 160 (accept_3_3 38 115 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 115 160 (Polychromatic418967fa.accept_7_2_3_6_1_4 37
  115 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 115 160
  (Polychromatic418967fa.accept_13_10_11_4_1_2248 36 115 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 115 160 5 7 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 34 115 160 (Polychromatic418967fa.accept_11_1_5_6_1_397 34 115 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 115 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 115 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 115 160 (accept_3_3 32 115 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 115 160 (Polychromatic418967fa.accept_19_12_1_8_1_4495 31 115 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 115 160 5 6 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 115 160 (accept_3_3 29 115 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 115 160 (Polychromatic418967fa.accept_13_2_11_4_1_445 28 115 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 115 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 115 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 115 160 (accept_3_3 26 115 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 115 160 5 5 23 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 115 160
  (Polychromatic418967fa.accept_14_10_3_6_1_2728 24 115 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 115 160 (accept_3_3 23 115 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 115 160 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 115 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 115 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 115 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 115 160 5 4 23 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 115 160
  (Polychromatic418967fa.accept_13_6_11_4_1_938 19 115 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 115 160 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 115 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 115 160 (accept_3_3 17 115 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 115 160 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 115 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 115 160 5 3 23 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 115 160 (accept_3_3 14 115 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 115 160 (Polychromatic418967fa.accept_19_13_1_8_1_3281 13 115
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 115 160
  (Polychromatic418967fa.accept_11_1_5_6_1_397 12 115 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 115 160 (accept_3_3 11 115 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  115 160 5 2 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 115 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 115 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 115 160 (accept_3_3 8 115 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 115 160 (Polychromatic418967fa.accept_13_7_11_4_1_2247 7 115 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 115 160 (Polychromatic418967fa.accept_13_6_11_4_1_938 6 115 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 115 160 5 1 23 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 115 160
  (Polychromatic418967fa.accept_7_4_3_6_1_340 4 115 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 115 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 115 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 160 (accept_3_3 2 115 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 115 160 (Polychromatic418967fa.accept_11_1_5_6_1_397 1 115 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115 160)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  47 114 160 (Eq.refl Bool.true) (allA_succ_of_gcd 46 114 160 2 23 57 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 114 160 (Polychromatic418967fa.accept_7_3_2_6_1_56 45
  114 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 114 160 2 22 57 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 114 160
  (Polychromatic418967fa.accept_7_1_2_6_1_55 43 114 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 114 160 2 21 57 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 114 160 (accept_3_3 41 114 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 114 160 2 20 57 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 114 160 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 114 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 114 160 2 19 57 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 114 160
  (Polychromatic418967fa.accept_9_1_6_7_1_285 37 114 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 114 160 2 18 57 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 114 160 (accept_3_3 35 114 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 114 160 2 17 57 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 114 160 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 114 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 114 160 2 16 57 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 114 160
  (Polychromatic418967fa.accept_7_3_2_6_1_56 31 114 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 114 160 2 15 57 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 114 160 (accept_3_3 29 114 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 114 160 2 14 57 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 114 160 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 114 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 114 160 2 13 57 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 114 160
  (Polychromatic418967fa.accept_7_4_2_6_1_337 25 114 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 114 160 2 12 57 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 114 160 (accept_3_3 23 114 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 114 160 2 11 57 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 114 160 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 114 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 114 160 2 10 57 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 114 160
  (Polychromatic418967fa.accept_9_1_6_7_1_285 19 114 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 160 2 9 57 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 114 160 (accept_3_3 17 114 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  114 160 2 8 57 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 114 160 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 114 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 114 160 2 7 57 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 114 160 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 114 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 114 160 2 6 57 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 114 160 (accept_3_3 11 114 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 114 160 2 5 57 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 114 160
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 114 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 114 160 2 4 57 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 114 160 (Polychromatic418967fa.accept_13_7_10_4_1_919 7 114 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114 160 2 3 57 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 114 160 (accept_3_3 5 114 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 114 160 2 2 57 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 114 160 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 114 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 114 160 2 1 57 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 160 (Polychromatic418967fa.accept_7_1_2_6_1_55 1
  114 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  160))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 113 160 (Eq.refl Bool.true) (allA_of_3_1 48 113 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 112 160 (Eq.refl Bool.true) (allA_succ_of_gcd 48 112 160 16 3
  7 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 112 160
  (accept_3_3 47 112 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 112 160 2 23 56 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 112 160
  (Polychromatic418967fa.accept_22_1_2_6_1_5427 45 112 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 112 160 4 11 28 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 112 160 (Polychromatic418967fa.accept_18_7_4_16_1_2299 43 112 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 112 160 2 21 56 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 112 160 (accept_3_3 41 112 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 112 160 8 5 14 20 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 112 160
  (Polychromatic418967fa.accept_9_3_4_7_1_89 39 112 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 112 160 2 19 56 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 112 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 112 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 112 160 4 9 28 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 112 160 (accept_3_3 35 112 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 112 160 2 17 56 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 112 160 (Polychromatic418967fa.accept_9_6_4_7_1_300 33
  112 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 112 160 16 2 7 10 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 112 160
  (Polychromatic418967fa.accept_15_1_7_10_1_287 31 112 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 112 160 2 15 56 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 112 160 (accept_3_3 29 112 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 112 160 4 7 28 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 112 160 (Polychromatic418967fa.accept_15_12_7_10_1_3297 27 112 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 112 160 2 13 56 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 112 160
  (Polychromatic418967fa.accept_13_12_8_4_1_3099 25 112 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 112 160 8 3 14 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 112 160 (accept_3_3 23 112 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  112 160 2 11 56 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 112 160 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 112 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 112 160 4 5 28 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 112 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 19
  112 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 112 160 2 9 56 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 112 160 (accept_3_3 17
  112 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 112 160 16 1 7 10 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 112 160
  (Polychromatic418967fa.accept_9_6_4_7_1_300 15 112 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 112 160 2 7 56 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 112 160 (Polychromatic418967fa.accept_25_13_12_10_1_8815 13 112 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 112 160 4 3 28 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 112 160 (accept_3_3 11 112 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 112 160 2 5 56 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 112 160 (Polychromatic418967fa.accept_13_9_8_4_1_937 9
  112 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 112 160 8 1 14 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 112 160
  (Polychromatic418967fa.accept_18_7_4_16_1_2299 7 112 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 112 160 2 3 56 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 112 160 (accept_3_3 5 112 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 112
  160 4 1 28 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  112 160 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 112 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 112 160 2 1 56 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 112 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 112 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112 160)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 50 111 160 (Eq.refl Bool.true) (allA_succ_of_accept 49 111 160 (Polychromatic418967fa.accept_6_1_3_4_1_1
  49 111 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 111 160
  (Polychromatic418967fa.accept_13_9_7_4_1_953 48 111 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 111 160 (accept_3_3 47 111 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 111 160 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 111 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 111 160 (Polychromatic418967fa.accept_13_6_7_4_1_2264 45 111 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 111 160 (accept_3_3 44 111 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 111 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 111 160
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 111 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 111 160 (accept_3_3 41 111 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 111 160 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 111 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 111 160 (Polychromatic418967fa.accept_17_5_9_7_1_6185 39 111 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 111 160 (accept_3_3 38 111 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 111 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 111 160
  (Polychromatic418967fa.accept_13_10_7_4_1_2262 36 111 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 111 160 (accept_3_3 35 111 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 111 160 (Polychromatic418967fa.accept_15_4_6_10_1_823 34 111 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 111 160 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 111 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 111 160 (accept_3_3 32 111 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 111 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 111 160
  (Polychromatic418967fa.accept_12_6_3_4_1_394 30 111 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 111 160 (accept_3_3 29 111 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 111 160 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 111 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 111 160 (Polychromatic418967fa.accept_11_5_1_6_1_774 27 111 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 111 160 (accept_3_3 26 111 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 111 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 160
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 111 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 111 160 (accept_3_3 23 111 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 111 160 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 111 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 111 160 (Polychromatic418967fa.accept_14_7_13_6_1_1177 21 111 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 111 160 (accept_3_3 20 111 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 111 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 160
  (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 111 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 111 160 (accept_3_3 17 111 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 111 160 (Polychromatic418967fa.accept_11_5_1_6_1_774 16 111 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 111 160 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 111 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 111 160 (accept_3_3 14 111 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 111 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 160
  (Polychromatic418967fa.accept_13_12_7_4_1_3124 12 111 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 111 160 (accept_3_3 11 111 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 111 160 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 111 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 111 160 (Polychromatic418967fa.accept_13_9_7_4_1_953 9 111 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 160 (accept_3_3 8 111 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 111 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 160
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 111 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 111 160 (accept_3_3 5 111 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  111 160 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 111 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 111 160 (Polychromatic418967fa.accept_13_3_7_4_1_435 3 111 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 160 (accept_3_3 2 111 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 111 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111
  160)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 110 160 (Eq.refl Bool.true) (allA_of_3_1 51 110
  160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 52 109 160 (Eq.refl Bool.true) (allA_succ_of_accept 51 109
  160 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 109 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 109 160 (accept_3_3 50 109 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 109 160 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 109 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 109 160 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 109 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 109 160 (accept_3_3 47 109 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 109 160 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 109 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 109 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 109 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 109 160 (accept_3_3 44 109 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 109 160 (Polychromatic418967fa.accept_15_13_4_10_1_821 43 109 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 109 160 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 109 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 109 160 (accept_3_3 41 109 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 109 160 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 109 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 109 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 109 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 109 160 (accept_3_3 38 109 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 109 160 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 109 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 109 160 (Polychromatic418967fa.accept_13_10_5_4_1_3107 36 109 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 109 160 (accept_3_3 35 109 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 109 160 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 109
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 109 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 109 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 109 160 (accept_3_3 32 109 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 109 160 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 109 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 109 160 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 109 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 109 160 (accept_3_3 29 109 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 109 160 (Polychromatic418967fa.accept_13_2_5_4_1_3926 28 109 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 109 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 109 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 109 160 (accept_3_3 26 109 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 109 160 (Polychromatic418967fa.accept_13_12_5_4_1_3133 25 109 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 109 160 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 109 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 109 160 (accept_3_3 23 109 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 109 160 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 109 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 109 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 109 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 109 160 (accept_3_3 20 109 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 109 160 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 109 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 109 160 (Polychromatic418967fa.accept_21_18_4_13_1_5602 18 109 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 109 160 (accept_3_3 17 109 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 109 160 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 109 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 109 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 109 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 109 160 (accept_3_3 14 109 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 109 160 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 109 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 109 160 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 109 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 109 160 (accept_3_3 11 109 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 109 160 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 109 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 109 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 109 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 109 160 (accept_3_3 8 109 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  109 160 (Polychromatic418967fa.accept_15_7_4_10_1_1513 7 109 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 109 160 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 109 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 109 160 (accept_3_3 5 109 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 109 160 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 109 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 109 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 109 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 109 160 (accept_3_3 2 109 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  109 160 (Polychromatic418967fa.accept_13_1_5_4_1_463 1 109 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 109 160)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 108 160 (Eq.refl
  Bool.true) (allA_succ_of_gcd 52 108 160 4 13 27 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 108 160 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 108 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 108 160 2 25 54 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 108 160
  (Polychromatic418967fa.accept_24_1_12_16_1_5184 49 108 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 108 160 4 12 27 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 108 160 (accept_3_3 47 108 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 108 160 2 23 54 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 108 160 (Polychromatic418967fa.accept_14_3_10_6_1_1136 45 108 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 108 160 4 11 27 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 108 160
  (Polychromatic418967fa.accept_15_13_3_10_1_2296 43 108 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 108 160 2 21 54 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 108 160 (accept_3_3 41 108 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 108 160 4 10 27 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 108 160 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 108 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 108 160 2 19 54 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 108 160
  (Polychromatic418967fa.accept_7_2_3_6_1_4 37 108 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 108 160 4 9 27 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 108 160 (accept_3_3 35 108 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  108 160 2 17 54 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 108 160 (Polychromatic418967fa.accept_17_16_6_7_1_2715 33 108 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 108 160 4 8 27 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 108 160 (Polychromatic418967fa.accept_14_3_10_6_1_1136
  31 108 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 108 160 2 15 54 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 108 160
  (accept_3_3 29 108 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 108 160 4 7 27 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 108 160
  (Polychromatic418967fa.accept_21_6_3_13_1_2742 27 108 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 108 160 2 13 54 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 108 160 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 108 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 108 160 4 6 27 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 108 160 (accept_3_3 23 108 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 108 160 2 11 54 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 108 160 (Polychromatic418967fa.accept_15_6_3_10_1_2341
  21 108 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 108 160 4 5 27 40
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 108 160
  (Polychromatic418967fa.accept_22_19_20_6_1_8814 19 108 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 108 160 2 9 54 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 108 160 (accept_3_3 17 108 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 108 160 4 4 27 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 108 160 (Polychromatic418967fa.accept_23_15_16_22_1_8813 15 108 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 108 160 2 7 54 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 108 160
  (Polychromatic418967fa.accept_15_13_3_10_1_2296 13 108 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 108 160 4 3 27 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 108 160 (accept_3_3 11 108 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 108 160 2 5 54 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 108 160 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 108 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 108 160 4 2 27 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 108 160 (Polychromatic418967fa.accept_15_7_3_10_1_817 7 108 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 160 2 3 54 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 160 (accept_3_3 5 108 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 108 160 4 1 27 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 108 160 (Polychromatic418967fa.accept_11_3_9_6_1_105 3
  108 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 108 160 2 1 54 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 108 160
  (Polychromatic418967fa.accept_19_1_13_8_1_8779 1 108 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 108 160))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 107 160 (Eq.refl Bool.true)
  (allA_of_3_1 54 107 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 55 106 160 (Eq.refl Bool.true)
  (allA_succ_of_gcd 54 106 160 2 27 53 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 106 160 (accept_3_3 53 106 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 106 160 2 26 53 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 106 160 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 106 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 106 160 2 25 53 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 106 160
  (Polychromatic418967fa.accept_12_1_10_4_1_380 49 106 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 106 160 2 24 53 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 106 160 (accept_3_3 47 106 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 106 160 2 23 53 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 106 160 (Polychromatic418967fa.accept_11_1_7_6_1_378 45 106 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 106 160 2 22 53 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 106 160
  (Polychromatic418967fa.accept_12_7_10_4_1_382 43 106 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 106 160 2 21 53 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 106 160 (accept_3_3 41 106 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 106 160 2 20 53 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 106 160 (Polychromatic418967fa.accept_15_9_1_10_1_4316 39 106 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 106 160 2 19 53 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 106 160
  (Polychromatic418967fa.accept_7_2_1_6_1_173 37 106 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 106 160 2 18 53 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 106 160 (accept_3_3 35 106 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 106 160 2 17 53 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 106 160 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 106 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 106 160 2 16 53 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 106 160
  (Polychromatic418967fa.accept_12_7_10_4_1_382 31 106 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 106 160 2 15 53 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 106 160 (accept_3_3 29 106 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 106 160 2 14 53 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 106 160 (Polychromatic418967fa.accept_24_3_10_16_1_6997 27 106 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 106 160 2 13 53 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 106 160
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 106 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 106 160 2 12 53 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 106 160 (accept_3_3 23 106 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 106 160 2 11 53 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 106 160 (Polychromatic418967fa.accept_14_7_8_6_1_1164 21 106 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 106 160 2 10 53 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 106 160
  (Polychromatic418967fa.accept_7_5_1_6_1_163 19 106 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 106 160 2 9 53 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 106 160 (accept_3_3 17 106 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  106 160 2 8 53 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 106 160 (Polychromatic418967fa.accept_23_15_14_22_1_3713 15 106 160 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 14 106 160 2 7 53 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 106 160 (Polychromatic418967fa.accept_12_1_10_4_1_380 13 106
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 106 160 2 6 53 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 106 160 (accept_3_3 11
  106 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 106 160 2 5 53 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 106 160
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 106 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 106 160 2 4 53 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 106 160 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 106 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 106 160 2 3 53 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 106 160 (accept_3_3 5 106 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 106 160 2 2 53 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 106 160 (Polychromatic418967fa.accept_17_3_4_7_1_1658 3 106 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 106 160 2 1 53 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 106 160 (Polychromatic418967fa.accept_11_1_7_6_1_378 1
  106 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106
  160))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 105 160 (Eq.refl Bool.true)
  (allA_succ_of_gcd 55 105 160 5 11 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 54 105 160 (Polychromatic418967fa.accept_12_6_9_4_1_96 54 105 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 105 160 (accept_3_3 53 105 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 105 160 (Polychromatic418967fa.accept_22_8_17_6_1_8769 52 105 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 105 160
  (Polychromatic418967fa.accept_24_3_9_16_1_8812 51 105 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 105 160 5 10 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 105 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 105 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 105 160 (Polychromatic418967fa.accept_9_3_6_7_1_562
  48 105 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 105 160 (accept_3_3 47
  105 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 105 160
  (Polychromatic418967fa.accept_9_1_6_7_1_285 46 105 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 105 160 5 9 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 105 160 (accept_3_3 44 105 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 105 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 105 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 105 160 (Polychromatic418967fa.accept_12_6_9_4_1_96 42 105 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 105 160 (accept_3_3 41 105 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 105 160 5 8 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 105 160 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 105 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 105 160 (accept_3_3 38 105 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 37
  105 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 105 160
  (Polychromatic418967fa.accept_13_10_1_4_1_3103 36 105 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 105 160 5 7 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 105 160 (Polychromatic418967fa.accept_22_12_17_6_1_8811 34 105 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 105 160
  (Polychromatic418967fa.accept_17_16_3_7_1_5028 33 105 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 105 160 (accept_3_3 32 105 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 105 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 105 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 105 160 5 6 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 105 160 (accept_3_3 29 105 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 105 160 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 105 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 105 160 (Polychromatic418967fa.accept_14_13_7_6_1_3525 27 105
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 160 (accept_3_3 26 105
  160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 105 160 5 5 21 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 105 160
  (Polychromatic418967fa.accept_18_6_15_16_1_7325 24 105 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 105 160 (accept_3_3 23 105 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 105 160 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 105 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 105 160 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 105 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 105 160 5 4 21 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 105 160
  (Polychromatic418967fa.accept_6_1_3_4_1_1 19 105 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 105 160 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 105 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 160 (accept_3_3 17 105 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 105 160 (Polychromatic418967fa.accept_13_3_1_4_1_945 16 105 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 105 160 5 3 21 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 105 160 (accept_3_3 14 105 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 13
  105 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 160
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 105 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 105 160 (accept_3_3 11 105 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  105 160 5 2 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 105 160 (Polychromatic418967fa.accept_18_9_15_16_1_8759 9 105 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 105 160 (accept_3_3 8 105 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 105 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 105 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 105 160 (Polychromatic418967fa.accept_12_6_9_4_1_96 6 105 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 105 160 5 1 21 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 105 160
  (Polychromatic418967fa.accept_9_4_6_7_1_286 4 105 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 105 160 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 105 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 160 (accept_3_3 2 105 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 105 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 105 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105 160))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 57 104 160 (Eq.refl Bool.true) (allA_of_3_1 57 104 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 58 103 160 (Eq.refl Bool.true) (allA_succ_of_accept 57 103 160 (Polychromatic418967fa.accept_6_3_1_4_1_25
  57 103 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 103 160 (accept_3_3 56
  103 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 103 160
  (Polychromatic418967fa.accept_9_1_4_7_1_7 55 103 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 103 160 (Polychromatic418967fa.accept_13_2_12_4_1_943 54 103 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 103 160 (accept_3_3 53 103 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 103 160 (Polychromatic418967fa.accept_22_8_15_6_1_8810 52 103 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 103 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 103 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 103 160 (accept_3_3 50 103 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 103 160 (Polychromatic418967fa.accept_15_4_13_10_1_1508 49 103 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 103 160 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 103 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 103 160 (accept_3_3 47 103 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 103 160 (Polychromatic418967fa.accept_7_4_5_6_1_344 46 103 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 103 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 103 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 103 160 (accept_3_3 44 103 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 103 160 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 103 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 103 160 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 103 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 103 160 (accept_3_3 41 103 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 103 160 (Polychromatic418967fa.accept_27_13_22_25_1_8809 40 103 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 103 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 103 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 103 160 (accept_3_3 38 103 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 103 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 103 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 103 160 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 103 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 103 160 (accept_3_3 35 103 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 103 160 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 103 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 103 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 103 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 103 160 (accept_3_3 32 103 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 103 160 (Polychromatic418967fa.accept_13_5_12_4_1_449 31 103 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 103 160 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 103 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 103 160 (accept_3_3 29 103 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 103 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 103 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 103 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 103 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 103 160 (accept_3_3 26 103 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 103 160 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 103 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 103 160 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 103 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 103 160 (accept_3_3 23 103 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 103 160 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 103 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 103 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 103 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 103 160 (accept_3_3 20 103 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 103 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 103 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 103 160 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 103 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 103 160 (accept_3_3 17 103 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 103 160 (Polychromatic418967fa.accept_13_3_12_4_1_110 16 103 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 103 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 103 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 103 160 (accept_3_3 14 103 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 103 160 (Polychromatic418967fa.accept_11_2_4_6_1_2412 13 103 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 103 160 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 103 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 103 160 (accept_3_3 11 103 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 103 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 103 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 103 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 103 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 103 160 (accept_3_3 8 103 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  103 160 (Polychromatic418967fa.accept_13_7_12_4_1_450 7 103 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 103 160 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 103 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 103 160 (accept_3_3 5 103 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 103 160 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 103 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 103 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 103 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 103 160 (accept_3_3 2 103 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  103 160 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 103 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 103 160)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 102 160
  (Eq.refl Bool.true) (allA_succ_of_gcd 58 102 160 2 29 51 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 102 160 (Polychromatic418967fa.accept_12_9_6_4_1_402 57 102 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 102 160 2 28 51 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 102 160
  (Polychromatic418967fa.accept_9_1_3_7_1_6 55 102 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 102 160 2 27 51 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 102 160 (accept_3_3 53 102 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 102 160 2 26 51 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 102 160 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 102 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 102 160 2 25 51 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 102 160
  (Polychromatic418967fa.accept_9_4_3_7_1_296 49 102 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 102 160 2 24 51 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 102 160 (accept_3_3 47 102 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 102 160 2 23 51 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 102 160 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 102 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 102 160 2 22 51 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 102 160
  (Polychromatic418967fa.accept_15_13_12_10_1_4352 43 102 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 102 160 2 21 51 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 102 160 (accept_3_3 41 102 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 102 160 2 20 51 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 102 160 (Polychromatic418967fa.accept_12_3_6_4_1_400 39 102 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 102 160 2 19 51 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 102 160
  (Polychromatic418967fa.accept_7_2_4_6_1_166 37 102 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 160 2 18 51 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 102 160 (accept_3_3 35 102 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 102 160 2 17 51 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 102 160 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 102 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 102 160 2 16 51 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 102 160
  (Polychromatic418967fa.accept_7_3_4_6_1_329 31 102 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 160 2 15 51 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 102 160 (accept_3_3 29 102 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 102 160 2 14 51 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 102 160 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 102 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 102 160 2 13 51 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 102 160
  (Polychromatic418967fa.accept_13_12_11_4_1_3111 25 102 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 102 160 2 12 51 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 102 160 (accept_3_3 23 102 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 102 160 2 11 51 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 102 160 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 102 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 102 160 2 10 51 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 102 160
  (Polychromatic418967fa.accept_7_5_4_6_1_167 19 102 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 160 2 9 51 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 102 160 (accept_3_3 17 102 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  102 160 2 8 51 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 102 160 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 102 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 102 160 2 7 51 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 102 160 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 102 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 102 160 2 6 51 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 102 160 (accept_3_3 11 102 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 102 160 2 5 51 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 102 160
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 102 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 102 160 2 4 51 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 102 160 (Polychromatic418967fa.accept_13_7_11_4_1_2247 7 102 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102 160 2 3 51 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 102 160 (accept_3_3 5 102 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 102 160 2 2 51 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 102 160 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 102 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 102 160 2 1 51 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 160 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 102
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  160))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 101 160 (Eq.refl Bool.true) (allA_of_3_1
  60 101 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 61 100 160 (Eq.refl Bool.true) (allA_succ_of_gcd 60
  100 160 20 3 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  59 100 160 (accept_3_3 59 100 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 100 160 2 29 50 80
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 100 160
  (Polychromatic418967fa.accept_7_1_2_6_1_55 57 100 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 100 160 4 14 25 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 55 100 160 5 11 20 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 54 100 160 2 27 50 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 100 160 (accept_3_3 53 100 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 100 160 4 13 25 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 100 160 (Polychromatic418967fa.accept_9_6_1_7_1_577 51 100 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 100 160 10 5 10 16 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 100 160
  (Polychromatic418967fa.accept_9_4_1_7_1_293 49 100 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 100 160 4 12 25 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 100 160 (accept_3_3 47 100 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 100 160 2 23 50 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 100 160 5 9 20 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 44 100 160 4 11 25 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 100 160 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 100 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 100 160 2 21 50 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 100 160 (accept_3_3 41 100 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 100 160 20 2 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 100 160 (Polychromatic418967fa.accept_7_4_2_6_1_337 39
  100 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 100 160 2 19 50 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 100 160
  (Polychromatic418967fa.accept_18_1_10_16_1_566 37 100 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 100 160 4 9 25 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 100 160 5 7 20 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 34 100 160 2 17 50 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 100 160 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 100 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 100 160 4 8 25 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 100 160
  (Polychromatic418967fa.accept_7_3_2_6_1_56 31 100 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 100 160 10 3 10 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 100 160 (accept_3_3 29 100 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 100 160 4 7 25 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 100 160 (Polychromatic418967fa.accept_11_5_1_6_1_774 27 100 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 100 160 2 13 50 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 100 160 5 5 20 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 100 160 4 6 25 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 100 160 (accept_3_3 23 100 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 100 160 2 11 50 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 100 160 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 100 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 100 160 20 1 5 8 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 100 160
  (Polychromatic418967fa.accept_13_6_9_4_1_2288 19 100 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 100 160 2 9 50 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 100 160 (accept_3_3 17 100 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  100 160 4 4 25 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15
  100 160 5 3 20 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14
  100 160 2 7 50 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  13 100 160 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 100 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 100 160 4 3 25 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 100 160 (accept_3_3 11 100 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 100 160 10 1 10 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 100 160 (Polychromatic418967fa.accept_17_9_15_7_1_6212 9 100 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 100 160 4 2 25 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 100 160 (Polychromatic418967fa.accept_11_7_1_6_1_1281 7
  100 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 100 160 2 3 50 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 100 160 5 1 20 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 100 160 4 1 25 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 100 160
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 100 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 100 160 2 1 50 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 100 160 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 100 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 100 160)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 62 99 160 (Eq.refl Bool.true) (allA_succ_of_accept 61 99 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 61
  99 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 99 160
  (Polychromatic418967fa.accept_19_3_4_8_1_8808 60 99 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 99 160 (accept_3_3 59 99 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  99 160 (Polychromatic418967fa.accept_7_2_1_6_1_173 58 99 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 99 160 (Polychromatic418967fa.accept_15_12_9_10_1_2326 57 99 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 99 160 (accept_3_3 56 99 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 99 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 99 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 99 160
  (Polychromatic418967fa.accept_7_5_1_6_1_163 54 99 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 99 160 (accept_3_3 53 99 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  99 160 (Polychromatic418967fa.accept_19_14_4_8_1_8807 52 99 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 99 160 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 99 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 99 160 (accept_3_3 50 99 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 99 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 99 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 99 160
  (Polychromatic418967fa.accept_13_9_8_4_1_937 48 99 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 99 160 (accept_3_3 47 99 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  99 160 (Polychromatic418967fa.accept_15_1_9_10_1_2327 46 99 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 99 160 (Polychromatic418967fa.accept_25_20_24_10_1_8806 45 99 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 99 160 (accept_3_3 44 99 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 99 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 99 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 99 160
  (Polychromatic418967fa.accept_12_6_3_4_1_394 42 99 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 99 160 (accept_3_3 41 99 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  99 160 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 99 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 99 160 (Polychromatic418967fa.accept_21_18_15_13_1_4130 39 99 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 99 160 (accept_3_3 38 99 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 99 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 99 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 99 160
  (Polychromatic418967fa.accept_13_10_8_4_1_3098 36 99 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 99 160 (accept_3_3 35 99 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  99 160 (Polychromatic418967fa.accept_15_4_9_10_1_5384 34 99 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 99 160 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 99 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 99 160 (accept_3_3 32 99 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 99 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 99 160
  (Polychromatic418967fa.accept_7_2_1_6_1_173 30 99 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 99 160 (accept_3_3 29 99 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  99 160 (Polychromatic418967fa.accept_19_9_4_8_1_8805 28 99 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 99 160 (Polychromatic418967fa.accept_15_12_9_10_1_2326 27 99 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 99 160 (accept_3_3 26 99 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 99 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 99 160
  (Polychromatic418967fa.accept_13_11_8_4_1_3950 24 99 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 99 160 (accept_3_3 23 99 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  99 160 (Polychromatic418967fa.accept_13_9_8_4_1_937 22 99 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 99 160 (Polychromatic418967fa.accept_14_7_1_6_1_3514 21 99 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 99 160 (accept_3_3 20 99 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 99 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 99 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 99 160
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 99 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 99 160 (accept_3_3 17 99 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  99 160 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 99 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 99 160 (Polychromatic418967fa.accept_18_15_9_16_1_6029 15 99 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 99 160 (accept_3_3 14 99 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 99 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 99 160
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 99 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 99 160 (accept_3_3 11 99 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  99 160 (Polychromatic418967fa.accept_13_10_8_4_1_3098 10 99 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 99 160 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 99 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 160 (accept_3_3 8 99 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 99 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99 160
  (Polychromatic418967fa.accept_12_6_3_4_1_394 6 99 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 99 160 (accept_3_3 5 99 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99
  160 (Polychromatic418967fa.accept_15_4_9_10_1_5384 4 99 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 99 160 (Polychromatic418967fa.accept_15_3_9_10_1_2325 3 99 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 160 (accept_3_3 2 99 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 99 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  160)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 98 160 (Eq.refl Bool.true)
  (allA_of_3_1 63 98 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 64 97 160 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 97 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 97 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 97 160 (accept_3_3 62 97 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 97 160 (Polychromatic418967fa.accept_13_9_6_4_1_2243 61 97 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 97 160 (Polychromatic418967fa.accept_22_16_9_6_1_8804
  60 97 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 97 160 (accept_3_3 59
  97 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 97 160
  (Polychromatic418967fa.accept_11_3_9_6_1_105 58 97 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 97 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 97 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 97 160 (accept_3_3 56 97 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 97 160 (Polychromatic418967fa.accept_17_4_12_7_1_8771 55 97 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 97 160
  (Polychromatic418967fa.accept_13_2_6_4_1_1593 54 97 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 97 160 (accept_3_3 53 97 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  97 160 (Polychromatic418967fa.accept_19_14_2_8_1_5925 52 97 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 97 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 97 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 97 160 (accept_3_3 50 97 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 97 160 (Polychromatic418967fa.accept_13_10_6_4_1_1583 49 97 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 97 160
  (Polychromatic418967fa.accept_13_9_6_4_1_2243 48 97 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 97 160 (accept_3_3 47 97 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  97 160 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 97 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 97 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 97 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 97 160 (accept_3_3 44 97 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 97 160 (Polychromatic418967fa.accept_19_5_2_8_1_8803 43 97 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 97 160
  (Polychromatic418967fa.accept_15_12_7_10_1_3297 42 97 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 97 160 (accept_3_3 41 97 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  97 160 (Polychromatic418967fa.accept_14_12_13_6_1_1140 40 97 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 97 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 97 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 97 160 (accept_3_3 38 97 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 97 160 (Polychromatic418967fa.accept_13_11_6_4_1_3121 37 97 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 97 160
  (Polychromatic418967fa.accept_11_3_9_6_1_105 36 97 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 97 160 (accept_3_3 35 97 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  97 160 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 97 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 97 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 97 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 97 160 (accept_3_3 32 97 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 97 160 (Polychromatic418967fa.accept_13_5_6_4_1_1582 31 97 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 97 160
  (Polychromatic418967fa.accept_19_11_2_8_1_8802 30 97 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 97 160 (accept_3_3 29 97 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  97 160 (Polychromatic418967fa.accept_13_2_6_4_1_1593 28 97 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 97 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 97 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 97 160 (accept_3_3 26 97 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 97 160 (Polychromatic418967fa.accept_11_3_9_6_1_105 25 97 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 97 160
  (Polychromatic418967fa.accept_13_11_6_4_1_3121 24 97 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 97 160 (accept_3_3 23 97 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  97 160 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 97 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 97 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 97 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 97 160 (accept_3_3 20 97 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 97 160 (Polychromatic418967fa.accept_14_5_13_6_1_3574 19 97 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 97 160
  (Polychromatic418967fa.accept_13_5_6_4_1_1582 18 97 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 97 160 (accept_3_3 17 97 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  97 160 (Polychromatic418967fa.accept_15_1_7_10_1_287 16 97 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 97 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 97 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 97 160 (accept_3_3 14 97 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 97 160 (Polychromatic418967fa.accept_19_13_2_8_1_4484 13 97 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 97 160
  (Polychromatic418967fa.accept_14_12_13_6_1_1140 12 97 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 97 160 (accept_3_3 11 97 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  97 160 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 97 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 97 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 97 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 160 (accept_3_3 8 97 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 97 160 (Polychromatic418967fa.accept_13_7_6_4_1_933 7 97 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 160
  (Polychromatic418967fa.accept_19_6_2_8_1_4496 6 97 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 97 160 (accept_3_3 5 97 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97
  160 (Polychromatic418967fa.accept_15_4_7_10_1_807 4 97 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 97 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 97 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 160 (accept_3_3 2 97 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 97 160 (Polychromatic418967fa.accept_15_1_7_10_1_287 1 97 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97
  160)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 96 160 (Eq.refl Bool.true)
  (allA_succ_of_gcd 64 96 160 32 2 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 96 160 (Polychromatic418967fa.accept_15_3_6_10_1_1539 63 96 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 96 160 2 31 48 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 96 160 (Polychromatic418967fa.accept_13_9_5_4_1_1591
  61 96 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 96 160 4 15 24 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 96 160 (accept_3_3 59
  96 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 96 160 2 29 48 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 96 160
  (Polychromatic418967fa.accept_7_1_5_6_1_59 57 96 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 96 160 8 7 12 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 96 160 (Polychromatic418967fa.accept_9_1_6_7_1_285 55 96 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 96 160 2 27 48 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 96 160 (accept_3_3 53 96 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 96 160 4 13 24 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 96 160 (Polychromatic418967fa.accept_13_12_5_4_1_3133 51 96 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 96 160 2 25 48 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 96 160
  (Polychromatic418967fa.accept_9_4_6_7_1_286 49 96 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 96 160 16 3 6 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 96 160 (accept_3_3 47 96 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 96
  160 2 23 48 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  96 160 (Polychromatic418967fa.accept_13_6_5_4_1_3924 45 96 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 96 160 4 11 24 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 96 160 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 96 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 96 160 2 21 48 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 96 160 (accept_3_3 41 96 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 96 160 8 5 12 20 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 96 160 (Polychromatic418967fa.accept_7_4_5_6_1_344 39
  96 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 96 160 2 19 48 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 96 160
  (Polychromatic418967fa.accept_9_1_6_7_1_285 37 96 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 96 160 4 9 24 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 96 160 (accept_3_3 35 96 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 96
  160 2 17 48 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  96 160 (Polychromatic418967fa.accept_15_3_6_10_1_1539 33 96 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 96 160 32 1 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 96 160 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 96 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 96 160 2 15 48 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 96 160 (accept_3_3 29 96 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 96 160 4 7 24 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 96 160 (Polychromatic418967fa.accept_13_1_5_4_1_463 27 96 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 96 160 2 13 48 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 96 160
  (Polychromatic418967fa.accept_7_4_5_6_1_344 25 96 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 96 160 8 3 12 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 96 160 (accept_3_3 23 96 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 96
  160 2 11 48 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  96 160 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 96 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 96 160 4 5 24 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 96 160 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 96 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 160 2 9 48 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 160 (accept_3_3 17 96 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 96 160 16 1 6 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 96 160 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 96 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 96 160 2 7 48 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 96 160
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 96 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 96 160 4 3 24 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 96 160 (accept_3_3 11 96 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 96
  160 2 5 48 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  96 160 (Polychromatic418967fa.accept_13_9_5_4_1_1591 9 96 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 96 160 8 1 12 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 96 160 (Polychromatic418967fa.accept_19_7_1_8_1_7300 7 96 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 160 2 3 48 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96 160 (accept_3_3 5 96 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 96 160 4 1 24 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 96 160 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 96 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 96 160 2 1 48 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 96 160
  (Polychromatic418967fa.accept_7_1_5_6_1_59 1 96 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 96 160))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 95 160 (Eq.refl
  Bool.true) (allA_of_3_1 66 95 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 67 94 160 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 94 160 2 33 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 94 160 (accept_3_3 65 94 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 94
  160 2 32 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63
  94 160 (Polychromatic418967fa.accept_25_13_19_10_1_3337 63 94 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 94 160 2 31 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 94 160 (Polychromatic418967fa.accept_12_1_10_4_1_380 61 94 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 94 160 2 30 47 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 94 160 (accept_3_3 59 94 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 94 160 2 29 47 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 94 160
  (Polychromatic418967fa.accept_9_3_4_7_1_89 57 94 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 94 160 2 28 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 94 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 94 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 94 160 2 27 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 94 160 (accept_3_3 53 94 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 94 160 2 26 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 94 160 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 94 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 94 160 2 25 47 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 94 160
  (Polychromatic418967fa.accept_12_1_10_4_1_380 49 94 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 94 160 2 24 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 94 160 (accept_3_3 47 94 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 94
  160 2 23 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  94 160 (Polychromatic418967fa.accept_14_3_10_6_1_1136 45 94 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 94 160 2 22 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 94 160 (Polychromatic418967fa.accept_12_7_10_4_1_382 43 94 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 94 160 2 21 47 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 94 160 (accept_3_3 41 94 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 94 160 2 20 47 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 94 160
  (Polychromatic418967fa.accept_7_4_3_6_1_340 39 94 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 94 160 2 19 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 94 160 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 94 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 94 160 2 18 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 94 160 (accept_3_3 35 94 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 94 160 2 17 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 94 160 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 94 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 94 160 2 16 47 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 94 160
  (Polychromatic418967fa.accept_12_7_10_4_1_382 31 94 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 94 160 2 15 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 94 160 (accept_3_3 29 94 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 94
  160 2 14 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  94 160 (Polychromatic418967fa.accept_13_1_3_4_1_925 27 94 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 94 160 2 13 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 94 160 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 94 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 94 160 2 12 47 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 94 160 (accept_3_3 23 94 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 94 160 2 11 47 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 94 160
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 94 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 94 160 2 10 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 94 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 94 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 94 160 2 9 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 94 160 (accept_3_3 17 94 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 94 160 2 8 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 94 160 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 94 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 94 160 2 7 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 94 160 (Polychromatic418967fa.accept_12_1_10_4_1_380
  13 94 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 94 160 2 6 47 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 94 160 (accept_3_3 11
  94 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 94 160 2 5 47 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 94 160
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 94 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 94 160 2 4 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 94 160 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 94 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 94 160 2 3 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 94 160 (accept_3_3 5 94 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 94 160 2 2 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 94 160 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 94 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 94 160 2 1 47 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 94 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 94
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94
  160))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 93 160 (Eq.refl Bool.true)
  (allA_succ_of_accept 67 93 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 93 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 93 160 (Polychromatic418967fa.accept_7_3_2_6_1_56 66 93 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 93 160 (accept_3_3 65 93 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 160 (Polychromatic418967fa.accept_7_1_2_6_1_55 64
  93 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 160
  (Polychromatic418967fa.accept_13_11_2_4_1_1590 63 93 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 93 160 (accept_3_3 62 93 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  93 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 93 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 93 160 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 93 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 93 160 (accept_3_3 59 93 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 160 (Polychromatic418967fa.accept_9_4_3_7_1_296 58 93 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 160
  (Polychromatic418967fa.accept_7_1_2_6_1_55 57 93 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 93 160 (accept_3_3 56 93 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  93 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 93 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 93 160 (Polychromatic418967fa.accept_11_10_5_6_1_1842 54 93 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 93 160 (accept_3_3 53 93 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 160 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 93 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 160
  (Polychromatic418967fa.accept_9_6_3_7_1_580 51 93 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 93 160 (accept_3_3 50 93 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  93 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 93 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 93 160 (Polychromatic418967fa.accept_17_14_8_7_1_6183 48 93 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 93 160 (accept_3_3 47 93 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 160 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 93 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 160
  (Polychromatic418967fa.accept_7_3_2_6_1_56 45 93 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 93 160 (accept_3_3 44 93 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  93 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 93 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 93 160 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 93 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 93 160 (accept_3_3 41 93 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 160 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 93 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 160
  (Polychromatic418967fa.accept_7_4_2_6_1_337 39 93 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 93 160 (accept_3_3 38 93 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  93 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 93 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 93 160 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 93 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 93 160 (accept_3_3 35 93 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 160 (Polychromatic418967fa.accept_11_1_5_6_1_397 34 93 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 160
  (Polychromatic418967fa.accept_9_6_3_7_1_580 33 93 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 93 160 (accept_3_3 32 93 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  93 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 93 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 93 160 (Polychromatic418967fa.accept_12_6_9_4_1_96 30 93 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 93 160 (accept_3_3 29 93 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 160 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 93 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 160
  (Polychromatic418967fa.accept_21_6_9_13_1_8780 27 93 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 93 160 (accept_3_3 26 93 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  93 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 93 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 93 160 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 93 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 93 160 (accept_3_3 23 93 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 160 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 93 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 160
  (Polychromatic418967fa.accept_11_10_5_6_1_1842 21 93 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 93 160 (accept_3_3 20 93 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  93 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 93 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 93 160 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 93 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 160 (accept_3_3 17 93 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 160 (Polychromatic418967fa.accept_17_16_8_7_1_4983 16 93 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 160
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 93 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 93 160 (accept_3_3 14 93 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  93 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 93 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 93 160 (Polychromatic418967fa.accept_11_1_5_6_1_397 12 93 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 160 (accept_3_3 11 93 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 160 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 93 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 160
  (Polychromatic418967fa.accept_15_9_3_10_1_2312 9 93 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 93 160 (accept_3_3 8 93 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93
  160 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 93 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 93 160 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 93 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 160 (accept_3_3 5 93 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 93 160 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 93 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93 160 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 93
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 160 (accept_3_3 2 93 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 93
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  160)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 92 160 (Eq.refl Bool.true)
  (allA_of_3_1 69 92 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 70 91 160 (Eq.refl Bool.true)
  (allA_succ_of_accept 69 91 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 91 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 91 160 (accept_3_3 68 91 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 91 160 (Polychromatic418967fa.accept_9_4_1_7_1_293 67 91 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 91 160 (Polychromatic418967fa.accept_9_3_1_7_1_97 66
  91 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 91 160 (accept_3_3 65 91
  160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 91 160
  (Polychromatic418967fa.accept_11_9_3_6_1_797 64 91 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 91 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 91 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 91 160 (accept_3_3 62 91 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 91 160 (Polychromatic418967fa.accept_18_7_1_16_1_578 61 91 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 91 160 (Polychromatic418967fa.accept_9_6_1_7_1_577 60
  91 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 91 160 (accept_3_3 59 91
  160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 91 160
  (Polychromatic418967fa.accept_9_4_1_7_1_293 58 91 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 91 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 91 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 91 160 (accept_3_3 56 91 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 91 160 (Polychromatic418967fa.accept_14_13_7_6_1_3525 55 91 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 91 160
  (Polychromatic418967fa.accept_15_9_1_10_1_4316 54 91 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 91 160 (accept_3_3 53 91 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  91 160 (Polychromatic418967fa.accept_11_8_3_6_1_1855 52 91 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 91 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 91 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 91 160 (accept_3_3 50 91 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 91 160 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 91 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 91 160
  (Polychromatic418967fa.accept_9_3_1_7_1_97 48 91 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 91 160 (accept_3_3 47 91 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  91 160 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 91 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 91 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 91 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 91 160 (accept_3_3 44 91 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 91 160 (Polychromatic418967fa.accept_14_1_7_6_1_3604 43 91 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 91 160
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 91 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 91 160 (accept_3_3 41 91 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  91 160 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 91 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 91 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 91 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 91 160 (accept_3_3 38 91 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 91 160 (Polychromatic418967fa.accept_15_7_1_10_1_305 37 91 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 91 160
  (Polychromatic418967fa.accept_14_8_7_6_1_1159 36 91 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 91 160 (accept_3_3 35 91 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  91 160 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 91 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 91 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 91 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 91 160 (accept_3_3 32 91 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 91 160 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 91 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 91 160
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 91 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 91 160 (accept_3_3 29 91 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  91 160 (Polychromatic418967fa.accept_15_13_1_10_1_816 28 91 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 91 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 91 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 91 160 (accept_3_3 26 91 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 91 160 (Polychromatic418967fa.accept_18_7_1_16_1_578 25 91 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 91 160
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 91 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 91 160 (accept_3_3 23 91 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  91 160 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 91 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 91 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 91 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 91 160 (accept_3_3 20 91 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 91 160 (Polychromatic418967fa.accept_11_8_3_6_1_1855 19 91 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 91 160
  (Polychromatic418967fa.accept_21_18_7_13_1_8801 18 91 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 91 160 (accept_3_3 17 91 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  91 160 (Polychromatic418967fa.accept_17_16_6_7_1_2715 16 91 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 91 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 91 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 91 160 (accept_3_3 14 91 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 91 160 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 91 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 91 160
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 91 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 91 160 (accept_3_3 11 91 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  91 160 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 91 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 91 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 91 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 160 (accept_3_3 8 91 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 91 160 (Polychromatic418967fa.accept_15_7_1_10_1_305 7 91 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 91 160
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 91 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 91 160 (accept_3_3 5 91 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91
  160 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 91 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 91 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 91 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 160 (accept_3_3 2 91 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 91 160 (Polychromatic418967fa.accept_14_1_7_6_1_3604 1 91 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91
  160)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 90 160 (Eq.refl Bool.true)
  (allA_succ_of_gcd 70 90 160 10 7 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 90 160 (Polychromatic418967fa.accept_12_9_6_4_1_402 69 90 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 90 160 2 34 45 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 90 160 (Polychromatic418967fa.accept_13_2_12_4_1_943
  67 90 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 90 160 2 33 45 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 90 160 5 13 18 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 90 160 2 32 45 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 90 160
  (Polychromatic418967fa.accept_12_3_6_4_1_400 63 90 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 90 160 2 31 45 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 90 160 (Polychromatic418967fa.accept_19_4_14_8_1_4510 61 90 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 90 160 10 6 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 90 160 (accept_3_3 59 90 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 90 160 2 29 45 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 90 160 (Polychromatic418967fa.accept_12_9_6_4_1_402 57 90 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 90 160 2 28 45 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 90 160 5 11 18 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 90 160 2 27 45 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 90 160 (accept_3_3 53 90 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 90 160 2 26 45 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 90 160
  (Polychromatic418967fa.accept_12_3_6_4_1_400 51 90 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 90 160 10 5 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 90 160 (Polychromatic418967fa.accept_17_15_5_7_1_2694 49 90 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 90 160 2 24 45 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 90 160 (accept_3_3 47 90 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 90 160 2 23 45 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 90 160 5 9 18 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 90 160 2 22 45 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 90 160 (Polychromatic418967fa.accept_17_9_5_7_1_3802 43 90 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 90 160 2 21 45 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 90 160 (accept_3_3 41
  90 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 90 160 10 4 9 16 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 90 160
  (Polychromatic418967fa.accept_12_3_6_4_1_400 39 90 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 90 160 2 19 45 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 90 160 (Polychromatic418967fa.accept_11_4_2_6_1_389 37 90 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 90 160 2 18 45 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 90 160 5 7 18 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 90 160 2 17 45 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 90 160 (Polychromatic418967fa.accept_12_9_6_4_1_402 33
  90 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 90 160 2 16 45 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 90 160
  (Polychromatic418967fa.accept_13_5_12_4_1_449 31 90 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 90 160 10 3 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 90 160 (accept_3_3 29 90 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 90
  160 2 14 45 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  90 160 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 90 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 90 160 2 13 45 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 25 90 160 5 5 18 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 90 160 2 12 45 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 90 160 (accept_3_3 23 90 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 90 160 2 11 45 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 90 160 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 90 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 90 160 10 2 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 90 160 (Polychromatic418967fa.accept_21_19_6_13_1_8800 19 90
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 90 160 2 9 45 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 90 160 (accept_3_3 17
  90 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90 160 2 8 45 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 90 160 5 3 18 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 90 160 2 7 45 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 90 160
  (Polychromatic418967fa.accept_19_13_14_8_1_4490 13 90 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 90 160 2 6 45 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 90 160 (accept_3_3 11 90 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 90
  160 10 1 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  90 160 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 90 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 90 160 2 4 45 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 90 160 (Polychromatic418967fa.accept_13_7_12_4_1_450 7 90 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 160 2 3 45 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 90 160 5 1 18 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 90 160 2 2 45 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 90 160 (Polychromatic418967fa.accept_12_3_6_4_1_400 3
  90 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 90 160 2 1 45 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 90 160
  (Polychromatic418967fa.accept_22_1_2_6_1_5427 1 90 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 90 160))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 89 160 (Eq.refl
  Bool.true) (allA_of_3_1 72 89 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 73 88 160 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 88 160 8 9 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 88 160 (accept_3_3 71 88 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 88
  160 2 35 44 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69
  88 160 (Polychromatic418967fa.accept_21_6_4_13_1_8740 69 88 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 88 160 4 17 22 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 88 160 (Polychromatic418967fa.accept_17_16_3_7_1_5028 67 88 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 88 160 2 33 44 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 88 160 (accept_3_3 65 88 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 88 160 8 8 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 88 160 (Polychromatic418967fa.accept_13_11_10_4_1_1565
  63 88 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 88 160 2 31 44 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 88 160
  (Polychromatic418967fa.accept_7_5_4_6_1_167 61 88 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 88 160 4 15 22 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 88 160 (accept_3_3 59 88 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 88
  160 2 29 44 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57
  88 160 (Polychromatic418967fa.accept_13_5_10_4_1_1564 57 88 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 88 160 8 7 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 88 160 (Polychromatic418967fa.accept_17_4_3_7_1_4971 55 88 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 88 160 2 27 44 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 88 160 (accept_3_3 53 88 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 88 160 4 13 22 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 88 160 (Polychromatic418967fa.accept_7_2_4_6_1_166 51
  88 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 88 160 2 25 44 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 88 160
  (Polychromatic418967fa.accept_15_4_13_10_1_1508 49 88 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 88 160 8 6 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 88 160 (accept_3_3 47 88 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 88
  160 2 23 44 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  88 160 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 88 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 88 160 4 11 22 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 88 160 (Polychromatic418967fa.accept_19_5_12_8_1_7273 43 88 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 88 160 2 21 44 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 88 160 (accept_3_3 41 88 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 88 160 8 5 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 88 160 (Polychromatic418967fa.accept_19_1_12_8_1_8799
  39 88 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 88 160 2 19 44 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 88 160
  (Polychromatic418967fa.accept_7_2_4_6_1_166 37 88 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 88 160 4 9 22 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 88 160 (accept_3_3 35 88 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 88
  160 2 17 44 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  88 160 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 88 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 88 160 8 4 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 88 160 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 88 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 88 160 2 15 44 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 88 160 (accept_3_3 29 88 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 88 160 4 7 22 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 88 160 (Polychromatic418967fa.accept_13_1_10_4_1_954 27 88 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 88 160 2 13 44 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 88 160
  (Polychromatic418967fa.accept_19_6_12_8_1_8798 25 88 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 88 160 8 3 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 88 160 (accept_3_3 23 88 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 88
  160 2 11 44 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  88 160 (Polychromatic418967fa.accept_13_8_10_4_1_2270 21 88 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 88 160 4 5 22 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 88 160 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 88 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 88 160 2 9 44 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 88 160 (accept_3_3 17 88 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 88 160 8 2 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 88 160 (Polychromatic418967fa.accept_19_15_12_8_1_5922 15 88 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 88 160 2 7 44 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 88 160
  (Polychromatic418967fa.accept_26_13_10_4_1_8797 13 88 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 88 160 4 3 22 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 88 160 (accept_3_3 11 88 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 88
  160 2 5 44 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  88 160 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 88 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 88 160 8 1 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 88 160 (Polychromatic418967fa.accept_13_7_10_4_1_919 7 88 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 88 160 2 3 44 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 88 160 (accept_3_3 5 88 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 88 160 4 1 22 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 88 160 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 88 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 88 160 2 1 44 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 88 160
  (Polychromatic418967fa.accept_13_1_10_4_1_954 1 88 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 88 160))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 87 160
  (Eq.refl Bool.true) (allA_succ_of_accept 73 87 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 87 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 87 160
  (Polychromatic418967fa.accept_7_2_3_6_1_4 72 87 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 87 160 (accept_3_3 71 87 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  87 160 (Polychromatic418967fa.accept_13_5_9_4_1_441 70 87 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 87 160 (Polychromatic418967fa.accept_15_9_12_10_1_809 69 87 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 87 160 (accept_3_3 68 87 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 87 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 87 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 87 160
  (Polychromatic418967fa.accept_9_3_6_7_1_562 66 87 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 87 160 (accept_3_3 65 87 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  87 160 (Polychromatic418967fa.accept_9_1_6_7_1_285 64 87 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 87 160 (Polychromatic418967fa.accept_17_12_2_7_1_3813 63 87 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 87 160 (accept_3_3 62 87 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 87 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 87 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 87 160
  (Polychromatic418967fa.accept_7_4_3_6_1_340 60 87 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 87 160 (accept_3_3 59 87 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  87 160 (Polychromatic418967fa.accept_7_2_3_6_1_4 58 87 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 87 160 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 87 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 87 160 (accept_3_3 56 87 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 87 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 87 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 87 160
  (Polychromatic418967fa.accept_12_6_3_4_1_394 54 87 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 87 160 (accept_3_3 53 87 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  87 160 (Polychromatic418967fa.accept_14_10_3_6_1_2728 52 87 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 87 160 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 87 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 87 160 (accept_3_3 50 87 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 87 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 87 160
  (Polychromatic418967fa.accept_9_3_6_7_1_562 48 87 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 87 160 (accept_3_3 47 87 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  87 160 (Polychromatic418967fa.accept_7_4_3_6_1_340 46 87 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 87 160 (Polychromatic418967fa.accept_13_6_9_4_1_2288 45 87 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 87 160 (accept_3_3 44 87 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 87 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 87 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 87 160
  (Polychromatic418967fa.accept_12_6_3_4_1_394 42 87 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 87 160 (accept_3_3 41 87 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  87 160 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 87 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 87 160 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 87 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 87 160 (accept_3_3 38 87 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 87 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 87 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 87 160
  (Polychromatic418967fa.accept_15_6_12_10_1_1543 36 87 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 87 160 (accept_3_3 35 87 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  87 160 (Polychromatic418967fa.accept_13_8_9_4_1_1552 34 87 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 87 160 (Polychromatic418967fa.accept_13_7_9_4_1_918 33 87 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 87 160 (accept_3_3 32 87 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 87 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 87 160
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 87 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 87 160 (accept_3_3 29 87 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  87 160 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 87 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 87 160 (Polychromatic418967fa.accept_11_5_10_6_1_793 27 87 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 87 160 (accept_3_3 26 87 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 87 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 87 160
  (Polychromatic418967fa.accept_14_10_3_6_1_2728 24 87 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 87 160 (accept_3_3 23 87 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  87 160 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 87 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 87 160 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 87 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 87 160 (accept_3_3 20 87 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 87 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 87 160
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 87 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 87 160 (accept_3_3 17 87 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  87 160 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 87 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 87 160 (Polychromatic418967fa.accept_17_15_2_7_1_7389 15 87 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 160 (accept_3_3 14 87 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 87 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 87 160
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 87 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 87 160 (accept_3_3 11 87 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  87 160 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 87 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 87 160 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 87 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 160 (accept_3_3 8 87 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 87 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87 160
  (Polychromatic418967fa.accept_12_6_3_4_1_394 6 87 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 87 160 (accept_3_3 5 87 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87
  160 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 87 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 87 160 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 87 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 160 (accept_3_3 2 87 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 87 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 87 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  160)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 86 160 (Eq.refl
  Bool.true) (allA_of_3_1 75 86 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 76 85 160 (Eq.refl Bool.true)
  (allA_succ_of_gcd 75 85 160 5 15 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 85 160 (accept_3_3 74 85 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  85 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 73 85 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 85 160 (Polychromatic418967fa.accept_7_2_1_6_1_173 72 85 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 85 160 (accept_3_3 71 85 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 70 85 160 5 14 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 85 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 85 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 85 160 (accept_3_3 68 85 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 85 160 (Polychromatic418967fa.accept_21_4_1_13_1_8751
  67 85 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 85 160
  (Polychromatic418967fa.accept_9_3_4_7_1_89 66 85 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 65 85 160 5 13 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 64 85 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 85 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 85 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 85 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 85 160 (accept_3_3 62 85 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 85 160 (Polychromatic418967fa.accept_7_5_1_6_1_163 61
  85 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 85 160 5 12 17 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 85 160 (accept_3_3 59
  85 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 85 160
  (Polychromatic418967fa.accept_7_2_1_6_1_173 58 85 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 85 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 85 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 85 160 (accept_3_3 56 85 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 55 85 160 5 11 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 54 85 160 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 85 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 85 160 (accept_3_3 53 85 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 85 160 (Polychromatic418967fa.accept_19_14_9_8_1_7271 52 85
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 85 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 85 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 85 160 5 10 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 85 160 (Polychromatic418967fa.accept_13_10_7_4_1_2262 49 85 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 85 160 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 85 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 85 160 (accept_3_3 47 85 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 85 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 46
  85 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 85 160 5 9 17 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 85 160 (accept_3_3 44
  85 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 160
  (Polychromatic418967fa.accept_26_17_7_4_1_8796 43 85 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 85 160 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 85 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 85 160 (accept_3_3 41 85 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 85 160 5 8 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 85 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 85 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 85 160 (accept_3_3 38 85 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 85 160 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 85 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 160
  (Polychromatic418967fa.accept_11_3_8_6_1_788 36 85 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 85 160 5 7 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 85 160 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 85 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 85 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 85 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 160 (accept_3_3 32 85 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 85 160
  (Polychromatic418967fa.accept_21_10_1_13_1_7167 31 85 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 85 160 5 6 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 85 160 (accept_3_3 29 85 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  85 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 85 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 85 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 85 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 160 (accept_3_3 26 85 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 25 85 160 5 5 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 24 85 160 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 85 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 85 160 (accept_3_3 23 85 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 85 160 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 85 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 85 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 85 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 85 160 5 4 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 85 160 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 85 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 160 (Polychromatic418967fa.accept_19_18_9_8_1_3267 18 85
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 85 160 (accept_3_3 17 85 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 85 160 (Polychromatic418967fa.accept_7_2_1_6_1_173 16
  85 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 85 160 5 3 17 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 85 160 (accept_3_3 14
  85 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 160
  (Polychromatic418967fa.accept_22_13_19_6_1_8795 13 85 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 85 160 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 85 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 85 160 (accept_3_3 11 85 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 85 160 5 2 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 85 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 85 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 160 (accept_3_3 8 85 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 160 (Polychromatic418967fa.accept_14_7_1_6_1_3514 7 85 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 160
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 85 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 85 160 5 1 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 85 160 (Polychromatic418967fa.accept_19_4_9_8_1_8794 4 85 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 85 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 85 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 160 (accept_3_3 2 85 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 85 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 85
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  160)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 84 160 (Eq.refl
  Bool.true) (allA_succ_of_gcd 76 84 160 4 19 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 84 160 (Polychromatic418967fa.accept_13_10_6_4_1_1583 75 84 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 84 160 2 37 42 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 84 160
  (Polychromatic418967fa.accept_9_1_3_7_1_6 73 84 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 84 160 4 18 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 84 160 (accept_3_3 71 84 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 84
  160 2 35 42 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69
  84 160 (Polychromatic418967fa.accept_9_6_3_7_1_580 69 84 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 84 160 4 17 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 84 160 (Polychromatic418967fa.accept_9_4_3_7_1_296 67 84 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 84 160 2 33 42 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 84 160 (accept_3_3 65 84 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 84 160 4 16 21 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 84 160
  (Polychromatic418967fa.accept_13_11_6_4_1_3121 63 84 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 84 160 2 31 42 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 84 160 (Polychromatic418967fa.accept_13_9_6_4_1_2243 61 84 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 84 160 4 15 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 84 160 (accept_3_3 59 84 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 58 84 160 2 29 42 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 84 160 (Polychromatic418967fa.accept_13_5_6_4_1_1582 57 84 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 84 160 4 14 21 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 84 160
  (Polychromatic418967fa.accept_9_1_3_7_1_6 55 84 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 84 160 2 27 42 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 84 160 (accept_3_3 53 84 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 84
  160 4 13 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  84 160 (Polychromatic418967fa.accept_9_6_3_7_1_580 51 84 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 84 160 2 25 42 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 84 160 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 84 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 84 160 4 12 21 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 84 160 (accept_3_3 47 84 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 84 160 2 23 42 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 84 160
  (Polychromatic418967fa.accept_11_1_7_6_1_378 45 84 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 84 160 4 11 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 84 160 (Polychromatic418967fa.accept_24_19_12_16_1_8793 43 84 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 160 2 21 42 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 160 (accept_3_3 41 84 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 84 160 4 10 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 84 160 (Polychromatic418967fa.accept_23_16_15_22_1_5332 39 84
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 84 160 2 19 42 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 84 160
  (Polychromatic418967fa.accept_9_1_3_7_1_6 37 84 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 84 160 4 9 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 84 160 (accept_3_3 35 84 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 84
  160 2 17 42 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  84 160 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 84 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 84 160 4 8 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 84 160 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 84 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84 160 2 15 42 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 84 160 (accept_3_3 29 84 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 84 160 4 7 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 84 160 (Polychromatic418967fa.accept_15_12_9_10_1_2326 27 84
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 84 160 2 13 42 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 84 160
  (Polychromatic418967fa.accept_17_8_16_7_1_8792 25 84 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 84 160 4 6 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 84 160 (accept_3_3 23 84 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 84
  160 2 11 42 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  84 160 (Polychromatic418967fa.accept_23_21_15_22_1_8791 21 84 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 84 160 4 5 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 84 160 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 84 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84 160 2 9 42 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 84 160 (accept_3_3 17 84 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 84 160 4 4 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 84 160 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 84 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 84 160 2 7 42 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 160
  (Polychromatic418967fa.accept_9_4_3_7_1_296 13 84 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 84 160 4 3 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 84 160 (accept_3_3 11 84 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84
  160 2 5 42 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  84 160 (Polychromatic418967fa.accept_13_9_6_4_1_2243 9 84 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 84 160 4 2 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 84 160 (Polychromatic418967fa.accept_13_7_6_4_1_933 7 84 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 160 2 3 42 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 160 (accept_3_3 5 84 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 84 160 4 1 21 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 84 160 (Polychromatic418967fa.accept_15_3_9_10_1_2325 3 84 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 84 160 2 1 42 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 160
  (Polychromatic418967fa.accept_9_1_3_7_1_6 1 84 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 84 160))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 78 83 160
  (Eq.refl Bool.true) (allA_of_3_1 78 83 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 79 82 160 (Eq.refl
  Bool.true) (allA_succ_of_gcd 78 82 160 2 39 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 82 160 (accept_3_3 77 82 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 82 160 2 38 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 75 82 160 (Polychromatic418967fa.accept_9_3_1_7_1_97 75 82 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 82 160 2 37 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 82 160 (Polychromatic418967fa.accept_12_1_10_4_1_380
  73 82 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 82 160 2 36 41 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 82 160 (accept_3_3 71
  82 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 82 160 2 35 41 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 82 160
  (Polychromatic418967fa.accept_9_6_1_7_1_577 69 82 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 82 160 2 34 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 82 160 (Polychromatic418967fa.accept_7_4_5_6_1_344 67 82 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 82 160 2 33 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 82 160 (accept_3_3 65 82 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 64 82 160 2 32 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 82 160 (Polychromatic418967fa.accept_15_3_7_10_1_2324 63 82 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 82 160 2 31 41 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 82 160
  (Polychromatic418967fa.accept_12_1_10_4_1_380 61 82 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 82 160 2 30 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 82 160 (accept_3_3 59 82 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 82
  160 2 29 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57
  82 160 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 82 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 82 160 2 28 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 82 160 (Polychromatic418967fa.accept_12_7_10_4_1_382 55 82 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 82 160 2 27 41 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 82 160 (accept_3_3 53 82 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 82 160 2 26 41 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 82 160
  (Polychromatic418967fa.accept_9_6_1_7_1_577 51 82 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 82 160 2 25 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 82 160 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 82 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 82 160 2 24 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 82 160 (accept_3_3 47 82 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 82 160 2 23 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 82 160 (Polychromatic418967fa.accept_11_1_5_6_1_397 45 82 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 82 160 2 22 41 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 82 160
  (Polychromatic418967fa.accept_7_1_5_6_1_59 43 82 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 82 160 2 21 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 82 160 (accept_3_3 41 82 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 82
  160 2 20 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  82 160 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 82 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 82 160 2 19 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 82 160 (Polychromatic418967fa.accept_12_1_10_4_1_380 37 82 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 82 160 2 18 41 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 82 160 (accept_3_3 35 82 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 82 160 2 17 41 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 82 160
  (Polychromatic418967fa.accept_9_6_1_7_1_577 33 82 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 82 160 2 16 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 82 160 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 82 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 82 160 2 15 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 82 160 (accept_3_3 29 82 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 82 160 2 14 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 82 160 (Polychromatic418967fa.accept_14_13_12_6_1_2735 27 82
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 82 160 2 13 41 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 82 160
  (Polychromatic418967fa.accept_7_4_5_6_1_344 25 82 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 82 160 2 12 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 82 160 (accept_3_3 23 82 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 82
  160 2 11 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  82 160 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 82 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 82 160 2 10 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 82 160 (Polychromatic418967fa.accept_12_7_10_4_1_382 19 82 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 82 160 2 9 41 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 82 160 (accept_3_3 17 82 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 82 160 2 8 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 82 160 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 82 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 82 160 2 7 41 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 82 160
  (Polychromatic418967fa.accept_9_4_1_7_1_293 13 82 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 82 160 2 6 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 82 160 (accept_3_3 11 82 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 82
  160 2 5 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  82 160 (Polychromatic418967fa.accept_22_9_16_6_1_2493 9 82 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 82 160 2 4 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 82 160 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 82 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 82 160 2 3 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 82 160 (accept_3_3 5 82 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 82 160 2 2 41 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 82 160 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 82 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 82 160 2 1 41 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 82 160
  (Polychromatic418967fa.accept_7_1_5_6_1_59 1 82 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 82 160))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 81 160
  (Eq.refl Bool.true) (allA_succ_of_accept 79 81 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 81 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 81 160
  (Polychromatic418967fa.accept_12_6_9_4_1_96 78 81 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 81 160 (accept_3_3 77 81 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  81 160 (Polychromatic418967fa.accept_15_1_6_10_1_23 76 81 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 81 160 (Polychromatic418967fa.accept_7_5_4_6_1_167 75 81 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 81 160 (accept_3_3 74 81 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 81 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 81 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 81 160
  (Polychromatic418967fa.accept_7_2_4_6_1_166 72 81 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 81 160 (accept_3_3 71 81 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  81 160 (Polychromatic418967fa.accept_17_2_13_7_1_5011 70 81 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 81 160 (Polychromatic418967fa.accept_18_15_9_16_1_6029 69 81 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 81 160 (accept_3_3 68 81 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 81 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 81 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 81 160
  (Polychromatic418967fa.accept_7_3_4_6_1_329 66 81 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 81 160 (accept_3_3 65 81 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  81 160 (Polychromatic418967fa.accept_13_12_3_4_1_928 64 81 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 81 160 (Polychromatic418967fa.accept_15_3_6_10_1_1539 63 81 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 81 160 (accept_3_3 62 81 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 81 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 81 160
  (Polychromatic418967fa.accept_19_3_5_8_1_8790 60 81 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 81 160 (accept_3_3 59 81 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  81 160 (Polychromatic418967fa.accept_7_2_4_6_1_166 58 81 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 81 160 (Polychromatic418967fa.accept_11_2_4_6_1_2412 57 81 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 81 160 (accept_3_3 56 81 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 81 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 81 160
  (Polychromatic418967fa.accept_7_5_4_6_1_167 54 81 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 81 160 (accept_3_3 53 81 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  81 160 (Polychromatic418967fa.accept_7_3_4_6_1_329 52 81 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 81 160 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 81 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 81 160 (accept_3_3 50 81 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 81 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 81 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 81 160
  (Polychromatic418967fa.accept_15_3_6_10_1_1539 48 81 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 81 160 (accept_3_3 47 81 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  81 160 (Polychromatic418967fa.accept_11_2_4_6_1_2412 46 81 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 81 160 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 81 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 81 160 (accept_3_3 44 81 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 81 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 81 160
  (Polychromatic418967fa.accept_12_6_9_4_1_96 42 81 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 81 160 (accept_3_3 41 81 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  81 160 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 81 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 81 160 (Polychromatic418967fa.accept_22_17_15_6_1_7102 39 81 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 81 160 (accept_3_3 38 81 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 81 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 81 160
  (Polychromatic418967fa.accept_17_2_13_7_1_5011 36 81 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 81 160 (accept_3_3 35 81 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  81 160 (Polychromatic418967fa.accept_15_4_6_10_1_823 34 81 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 81 160 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 81 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 81 160 (accept_3_3 32 81 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 81 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 81 160
  (Polychromatic418967fa.accept_7_2_4_6_1_166 30 81 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 81 160 (accept_3_3 29 81 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  81 160 (Polychromatic418967fa.accept_17_11_13_7_1_3795 28 81 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 81 160 (Polychromatic418967fa.accept_13_1_3_4_1_925 27 81 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 81 160 (accept_3_3 26 81 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 81 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 81 160
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 81 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 81 160 (accept_3_3 23 81 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  81 160 (Polychromatic418967fa.accept_19_3_5_8_1_8790 22 81 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 81 160 (Polychromatic418967fa.accept_19_2_5_8_1_2081 21 81 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 81 160 (accept_3_3 20 81 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 81 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 81 160
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 81 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 81 160 (accept_3_3 17 81 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  81 160 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 81 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 81 160 (Polychromatic418967fa.accept_18_15_9_16_1_6029 15 81 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 81 160 (accept_3_3 14 81 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 81 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 81 160
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 81 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 81 160 (accept_3_3 11 81 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  81 160 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 81 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 81 160 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 81 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 81 160 (accept_3_3 8 81 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 81 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 160
  (Polychromatic418967fa.accept_12_6_9_4_1_96 6 81 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 81 160 (accept_3_3 5 81 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81
  160 (Polychromatic418967fa.accept_15_4_6_10_1_823 4 81 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 81 160 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 81 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 160 (accept_3_3 2 81 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 81 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81
  160)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 160 (allA_of_3_1 80
  80 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 79 160 (allA_succ_of_accept 78 79 160
  (Polychromatic418967fa.accept_7_1_2_6_1_55 78 79 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 79 160 (accept_3_3 77 79 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  79 160 (Polychromatic418967fa.accept_18_4_7_16_1_2307 76 79 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 79 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 79 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 79 160 (accept_3_3 74 79 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 79 160 (Polychromatic418967fa.accept_7_3_2_6_1_56 73 79 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 79 160
  (Polychromatic418967fa.accept_19_15_3_8_1_8789 72 79 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 79 160 (accept_3_3 71 79 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  79 160 (Polychromatic418967fa.accept_11_4_2_6_1_389 70 79 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 79 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 79 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 79 160 (accept_3_3 68 79 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 79 160 (Polychromatic418967fa.accept_7_4_2_6_1_337 67 79 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 79 160
  (Polychromatic418967fa.accept_7_3_2_6_1_56 66 79 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 79 160 (accept_3_3 65 79 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  79 160 (Polychromatic418967fa.accept_7_1_2_6_1_55 64 79 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 79 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 79 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 79 160 (accept_3_3 62 79 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 79 160 (Polychromatic418967fa.accept_19_4_3_8_1_8788 61 79 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 79 160
  (Polychromatic418967fa.accept_7_4_2_6_1_337 60 79 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 79 160 (accept_3_3 59 79 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  79 160 (Polychromatic418967fa.accept_12_10_7_4_1_820 58 79 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 79 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 79 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 79 160 (accept_3_3 56 79 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 79 160 (Polychromatic418967fa.accept_13_3_1_4_1_945 55 79 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 79 160
  (Polychromatic418967fa.accept_15_9_4_10_1_2316 54 79 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 79 160 (accept_3_3 53 79 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  79 160 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 79 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 79 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 79 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 79 160 (accept_3_3 50 79 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 79 160 (Polychromatic418967fa.accept_13_10_1_4_1_3103 49 79 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 79 160
  (Polychromatic418967fa.accept_11_4_2_6_1_389 48 79 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 79 160 (accept_3_3 47 79 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  79 160 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 79 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 79 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 79 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 79 160 (accept_3_3 44 79 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 79 160 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 79 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 79 160
  (Polychromatic418967fa.accept_13_3_1_4_1_945 42 79 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 79 160 (accept_3_3 41 79 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  79 160 (Polychromatic418967fa.accept_18_4_7_16_1_2307 40 79 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 79 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 79 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 79 160 (accept_3_3 38 79 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 79 160 (Polychromatic418967fa.accept_11_4_2_6_1_389 37 79 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 79 160
  (Polychromatic418967fa.accept_7_1_2_6_1_55 36 79 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 79 160 (accept_3_3 35 79 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  79 160 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 79 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 79 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 79 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 79 160 (accept_3_3 32 79 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 79 160 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 79 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 79 160
  (Polychromatic418967fa.accept_17_13_11_7_1_4961 30 79 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 79 160 (accept_3_3 29 79 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  79 160 (Polychromatic418967fa.accept_15_13_4_10_1_821 28 79 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 79 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 79 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 160 (accept_3_3 26 79 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 160 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 79 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 79 160
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 79 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 79 160 (accept_3_3 23 79 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  79 160 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 79 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 79 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 79 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 160 (accept_3_3 20 79 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 160 (Polychromatic418967fa.accept_18_1_7_16_1_1342 19 79 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 160
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 79 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 79 160 (accept_3_3 17 79 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  79 160 (Polychromatic418967fa.accept_13_3_1_4_1_945 16 79 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 79 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 79 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 160 (accept_3_3 14 79 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 160 (Polychromatic418967fa.accept_15_13_4_10_1_821 13 79 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 160
  (Polychromatic418967fa.accept_23_12_10_22_1_8787 12 79 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 79 160 (accept_3_3 11 79 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 79 160 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 79 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 79 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 79 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 160 (accept_3_3 8 79 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 160 (Polychromatic418967fa.accept_15_7_4_10_1_1513
  7 79 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 160
  (Polychromatic418967fa.accept_15_6_4_10_1_2319 6 79 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 160 (accept_3_3 5 79 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  160 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 79 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 79 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 79 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 160 (accept_3_3 2 79 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 79 160 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 79 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79
  160))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 78 160
  (allA_succ_of_accept 77 78 160 (accept_3_3 77 78 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 78
  160 2 38 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75
  78 160 (Polychromatic418967fa.accept_7_5_1_6_1_163 75 78 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 78 160 2 37 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 78 160 (Polychromatic418967fa.accept_9_1_6_7_1_285 73 78 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 160 2 36 39 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 160 (accept_3_3 71 78 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 78 160 2 35 39 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 78 160
  (Polychromatic418967fa.accept_12_9_6_4_1_402 69 78 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 78 160 2 34 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 78 160 (Polychromatic418967fa.accept_9_4_6_7_1_286 67 78 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78 160 2 33 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 78 160 (accept_3_3 65 78 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 64 78 160 2 32 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 78 160 (Polychromatic418967fa.accept_12_3_6_4_1_400 63 78 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 78 160 2 31 39 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 78 160
  (Polychromatic418967fa.accept_7_5_1_6_1_163 61 78 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 78 160 2 30 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 78 160 (accept_3_3 59 78 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 78
  160 2 29 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57
  78 160 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 78 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 78 160 2 28 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 78 160 (Polychromatic418967fa.accept_9_1_6_7_1_285 55 78 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 78 160 2 27 39 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 78 160 (accept_3_3 53 78 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 78 160 2 26 39 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 78 160
  (Polychromatic418967fa.accept_7_2_1_6_1_173 51 78 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 78 160 2 25 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 78 160 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 78 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 78 160 2 24 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 78 160 (accept_3_3 47 78 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 78 160 2 23 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 78 160 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 78 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 78 160 2 22 39 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 78 160
  (Polychromatic418967fa.accept_15_13_3_10_1_2296 43 78 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 78 160 2 21 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 78 160 (accept_3_3 41 78 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 78
  160 2 20 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  78 160 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 78 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 78 160 2 19 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 78 160 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 78 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78 160 2 18 39 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 78 160 (accept_3_3 35 78 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 78 160 2 17 39 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 78 160
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 78 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 78 160 2 16 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 78 160 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 78 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 78 160 2 15 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 78 160 (accept_3_3 29 78 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 78 160 2 14 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 78 160 (Polychromatic418967fa.accept_11_5_1_6_1_774 27 78 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 78 160 2 13 39 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 78 160
  (Polychromatic418967fa.accept_19_6_2_8_1_4496 25 78 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 78 160 2 12 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 78 160 (accept_3_3 23 78 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 78
  160 2 11 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  78 160 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 78 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 78 160 2 10 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 78 160 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 78 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 160 2 9 39 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 160 (accept_3_3 17 78 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78 160 2 8 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 78 160 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 78 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 78 160 2 7 39 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 78 160
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 78 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 78 160 2 6 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 78 160 (accept_3_3 11 78 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 78
  160 2 5 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  78 160 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 78 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 78 160 2 4 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 78 160 (Polychromatic418967fa.accept_11_7_1_6_1_1281 7 78 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 160 2 3 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 160 (accept_3_3 5 78 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 160 2 2 39 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 78 160 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 78 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 78 160 2 1 39 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 160
  (Polychromatic418967fa.accept_9_1_6_7_1_285 1 78 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 78 160)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 160
  (allA_of_3_1 77 77 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 76 160 (allA_succ_of_accept 75 76 160
  (Polychromatic418967fa.accept_9_3_4_7_1_89 75 76 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 76 160 2 37 38 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 73 76 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 73 76 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 76 160 4 18 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 76 160 (accept_3_3 71 76 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 70 76 160 2 35 38 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 76 160 (Polychromatic418967fa.accept_9_6_4_7_1_300 69 76 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 76 160 4 17 19 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 76 160
  (Polychromatic418967fa.accept_13_2_11_4_1_445 67 76 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 76 160 2 33 38 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 76 160 (accept_3_3 65 76 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 76
  160 4 16 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63
  76 160 (Polychromatic418967fa.accept_24_15_4_16_1_8786 63 76 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 76 160 2 31 38 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 76 160 (Polychromatic418967fa.accept_18_7_4_16_1_2299 61 76 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 76 160 4 15 19 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 76 160 (accept_3_3 59 76 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 76 160 2 29 38 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 76 160
  (Polychromatic418967fa.accept_9_3_4_7_1_89 57 76 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 76 160 4 14 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 76 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 76 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 76 160 2 27 38 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 76 160 (accept_3_3 53 76 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 76 160 4 13 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 76 160 (Polychromatic418967fa.accept_9_6_4_7_1_300 51 76 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 76 160 2 25 38 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 76 160
  (Polychromatic418967fa.accept_11_5_10_6_1_793 49 76 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 76 160 4 12 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 76 160 (accept_3_3 47 76 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 76
  160 2 23 38 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  76 160 (Polychromatic418967fa.accept_13_6_11_4_1_938 45 76 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 76 160 4 11 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 76 160 (Polychromatic418967fa.accept_15_13_1_10_1_816 43 76 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 76 160 2 21 38 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 76 160 (accept_3_3 41 76 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 76 160 4 10 19 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 76 160
  (Polychromatic418967fa.accept_9_3_4_7_1_89 39 76 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 76 160 2 19 38 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 76 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 76 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 76 160 4 9 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 76 160 (accept_3_3 35 76 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 76 160 2 17 38 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 76 160 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 76 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 76 160 4 8 19 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 76 160
  (Polychromatic418967fa.accept_17_14_8_7_1_6183 31 76 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 76 160 2 15 38 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 76 160 (accept_3_3 29 76 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 76
  160 4 7 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  76 160 (Polychromatic418967fa.accept_11_5_10_6_1_793 27 76 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 76 160 2 13 38 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 76 160 (Polychromatic418967fa.accept_13_12_11_4_1_3111 25 76 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 76 160 4 6 19 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 76 160 (accept_3_3 23 76 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 76 160 2 11 38 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 76 160 (Polychromatic418967fa.accept_9_3_4_7_1_89 21
  76 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 76 160 4 5 19 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 76 160
  (Polychromatic418967fa.accept_9_1_4_7_1_7 19 76 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 76 160 2 9 38 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 76 160 (accept_3_3 17 76 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 76
  160 4 4 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  76 160 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 76 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 76 160 2 7 38 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 76 160 (Polychromatic418967fa.accept_15_13_1_10_1_816 13 76 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 76 160 4 3 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 76 160 (accept_3_3 11 76 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 76 160 2 5 38 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 76 160 (Polychromatic418967fa.accept_15_9_1_10_1_4316 9 76 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 76 160 4 2 19 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 76 160
  (Polychromatic418967fa.accept_13_7_11_4_1_2247 7 76 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 76 160 2 3 38 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 76 160 (accept_3_3 5 76 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 76 160
  4 1 19 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 76
  160 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 76 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 76 160 2 1 38 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 76 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 76 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 76
  160)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 160 (allA_succ_of_accept
  74 75 160 (accept_3_3 74 75 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 75 160
  (Polychromatic418967fa.accept_6_1_3_4_1_1 73 75 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 75 160 (Polychromatic418967fa.accept_13_7_10_4_1_919 72 75 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 75 160 (accept_3_3 71 75 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 75 160 5 14 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 69 75 160 (Polychromatic418967fa.accept_9_6_3_7_1_580 69 75 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 160 (accept_3_3 68 75 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 75 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 75 160
  (Polychromatic418967fa.accept_12_6_3_4_1_394 66 75 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 65 75 160 5 13 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 64 75 160 (Polychromatic418967fa.accept_7_1_5_6_1_59 64 75 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 160 (Polychromatic418967fa.accept_13_11_10_4_1_1565 63 75
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 160 (accept_3_3 62 75 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 75 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 61
  75 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 75 160 5 12 15 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 75 160 (accept_3_3 59
  75 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 160
  (Polychromatic418967fa.accept_9_4_3_7_1_296 58 75 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 75 160 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 75 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 160 (accept_3_3 56 75 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 55 75 160 5 11 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 54 75 160 (Polychromatic418967fa.accept_12_6_3_4_1_394 54 75 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 75 160 (accept_3_3 53 75 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 160 (Polychromatic418967fa.accept_22_8_9_6_1_8785 52 75 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 160
  (Polychromatic418967fa.accept_9_6_3_7_1_580 51 75 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 75 160 5 10 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 75 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 75 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 75 160 (Polychromatic418967fa.accept_19_10_18_8_1_3238 48 75
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 75 160 (accept_3_3 47 75 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 160 (Polychromatic418967fa.accept_7_4_5_6_1_344 46
  75 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 75 160 5 9 15 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 75 160 (accept_3_3 44
  75 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 160
  (Polychromatic418967fa.accept_6_1_3_4_1_1 43 75 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 75 160 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 75 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 75 160 (accept_3_3 41 75 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 75 160 5 8 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 75 160 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 75 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 160 (accept_3_3 38 75 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 75 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 75 160
  (Polychromatic418967fa.accept_7_1_5_6_1_59 36 75 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 75 160 5 7 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 75 160 (Polychromatic418967fa.accept_13_8_10_4_1_2270 34 75 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 160 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 75 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 160 (accept_3_3 32 75 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 31
  75 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 75 160 5 6 15 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 75 160 (accept_3_3 29
  75 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 160
  (Polychromatic418967fa.accept_9_1_3_7_1_6 28 75 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 75 160 (Polychromatic418967fa.accept_13_1_10_4_1_954 27 75 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 160 (accept_3_3 26 75 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 75 160 5 5 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 24 75 160 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 75 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 75 160 (accept_3_3 23 75 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 160 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 75 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 160
  (Polychromatic418967fa.accept_13_8_10_4_1_2270 21 75 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 75 160 5 4 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 75 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 75 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 160 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 75 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 160 (accept_3_3 17 75 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 160
  (Polychromatic418967fa.accept_19_16_18_8_1_8784 16 75 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 75 160 5 3 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 75 160 (accept_3_3 14 75 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  75 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 75 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 75 160 (Polychromatic418967fa.accept_23_12_6_22_1_8783 12 75 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 160 (accept_3_3 11 75 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 75 160 5 2 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 75 160 (Polychromatic418967fa.accept_19_9_18_8_1_8782 9 75 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 160 (accept_3_3 8 75 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 75
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 160
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 75 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 75 160 5 1 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 75 160 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 75 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 75 160 (Polychromatic418967fa.accept_11_3_9_6_1_105 3 75 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 160 (accept_3_3 2 75 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 75
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  160))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 160 (allA_of_3_1 74 74
  160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 73 160 (allA_succ_of_accept 72 73 160
  (Polychromatic418967fa.accept_7_2_3_6_1_4 72 73 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 73 160 (accept_3_3 71 73 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  73 160 (Polychromatic418967fa.accept_12_10_1_4_1_392 70 73 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 73 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 73 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 160 (accept_3_3 68 73 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 160 (Polychromatic418967fa.accept_7_4_3_6_1_340 67 73 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 160
  (Polychromatic418967fa.accept_9_3_1_7_1_97 66 73 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 73 160 (accept_3_3 65 73 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  73 160 (Polychromatic418967fa.accept_13_12_8_4_1_3099 64 73 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 73 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 73 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 160 (accept_3_3 62 73 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 160 (Polychromatic418967fa.accept_13_9_8_4_1_937 61 73 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 160
  (Polychromatic418967fa.accept_7_4_3_6_1_340 60 73 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 160 (accept_3_3 59 73 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 160 (Polychromatic418967fa.accept_7_2_3_6_1_4 58 73 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 73 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 160 (accept_3_3 56 73 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 160 (Polychromatic418967fa.accept_19_17_16_8_1_2099 55 73 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 160
  (Polychromatic418967fa.accept_23_8_4_22_1_8781 54 73 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 160 (accept_3_3 53 73 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 160 (Polychromatic418967fa.accept_14_10_3_6_1_2728 52 73 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 73 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 160 (accept_3_3 50 73 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 160 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 73 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 160
  (Polychromatic418967fa.accept_9_3_1_7_1_97 48 73 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 160 (accept_3_3 47 73 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 160 (Polychromatic418967fa.accept_7_4_3_6_1_340 46 73 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 73 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 160 (accept_3_3 44 73 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 160 (Polychromatic418967fa.accept_17_9_5_7_1_3802 43 73 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 160
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 73 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 160 (accept_3_3 41 73 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 160 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 73 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 73 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 160 (accept_3_3 38 73 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 160 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 73 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 160
  (Polychromatic418967fa.accept_13_10_8_4_1_3098 36 73 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 160 (accept_3_3 35 73 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 160 (Polychromatic418967fa.accept_11_1_7_6_1_378 34 73 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 73 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 160 (accept_3_3 32 73 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 160 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 73 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 160
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 73 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 160 (accept_3_3 29 73 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 160 (Polychromatic418967fa.accept_17_11_5_7_1_6177 28 73 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 73 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 160 (accept_3_3 26 73 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 160 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 73 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 160
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 73 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 160 (accept_3_3 23 73 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 160 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 73 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 73 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 160 (accept_3_3 20 73 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 160 (Polychromatic418967fa.accept_15_4_13_10_1_1508 19 73 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 160
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 73 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 160 (accept_3_3 17 73 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 160 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 73 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 73 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 160 (accept_3_3 14 73 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 160 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 73 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 160
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 73 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 160 (accept_3_3 11 73 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 160 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 73 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 73 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 160 (accept_3_3 8 73 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 160 (Polychromatic418967fa.accept_18_7_1_16_1_578 7 73 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 160
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 73 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 160 (accept_3_3 5 73 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  160 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 73 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 73 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 160 (accept_3_3 2 73 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 160 (Polychromatic418967fa.accept_11_1_7_6_1_378 1 73 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  160))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 160 (allA_succ_of_accept 71
  72 160 (accept_3_3 71 72 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 72 160 2 35 36 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 72 160
  (Polychromatic418967fa.accept_15_9_12_10_1_809 69 72 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 72 160 4 17 18 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 72 160 (Polychromatic418967fa.accept_7_4_2_6_1_337 67 72 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 160 2 33 36 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 160 (accept_3_3 65 72 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 64 72 160 8 8 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 72 160 (Polychromatic418967fa.accept_13_11_7_4_1_1561 63 72 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 72 160 2 31 36 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 72 160
  (Polychromatic418967fa.accept_13_9_7_4_1_953 61 72 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 72 160 4 15 18 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 72 160 (accept_3_3 59 72 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 72
  160 2 29 36 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57
  72 160 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 72 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 72 160 8 7 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 72 160 (Polychromatic418967fa.accept_13_3_7_4_1_435 55 72 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 72 160 2 27 36 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 72 160 (accept_3_3 53 72 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 72 160 4 13 18 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 72 160 (Polychromatic418967fa.accept_13_12_7_4_1_3124
  51 72 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 72 160 2 25 36 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 72 160
  (Polychromatic418967fa.accept_13_10_7_4_1_2262 49 72 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 72 160 8 6 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 72 160 (accept_3_3 47 72 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 72
  160 2 23 36 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  72 160 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 72 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 72 160 4 11 18 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 72 160 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 72 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72 160 2 21 36 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 72 160 (accept_3_3 41 72 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 72 160 8 5 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 72 160 (Polychromatic418967fa.accept_7_4_2_6_1_337 39
  72 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 72 160 2 19 36 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 72 160
  (Polychromatic418967fa.accept_13_11_7_4_1_1561 37 72 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 72 160 4 9 18 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 72 160 (accept_3_3 35 72 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 72
  160 2 17 36 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  72 160 (Polychromatic418967fa.accept_21_12_9_13_1_4091 33 72 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 72 160 8 4 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 72 160 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 72 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 160 2 15 36 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 160 (accept_3_3 29 72 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 72 160 4 7 18 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 72 160 (Polychromatic418967fa.accept_21_6_9_13_1_8780 27 72 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 72 160 2 13 36 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 160
  (Polychromatic418967fa.accept_7_4_2_6_1_337 25 72 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 72 160 8 3 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 72 160 (accept_3_3 23 72 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72
  160 2 11 36 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  72 160 (Polychromatic418967fa.accept_15_6_12_10_1_1543 21 72 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 72 160 4 5 18 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 72 160 (Polychromatic418967fa.accept_13_6_7_4_1_2264 19 72 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72 160 2 9 36 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 72 160 (accept_3_3 17 72 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 72 160 8 2 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 72 160 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 72 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 72 160 2 7 36 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 160
  (Polychromatic418967fa.accept_15_13_12_10_1_4352 13 72 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 72 160 4 3 18 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 72 160 (accept_3_3 11 72 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 72 160 2 5 36 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 72 160 (Polychromatic418967fa.accept_13_9_7_4_1_953 9 72 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 72 160 8 1 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 72 160 (Polychromatic418967fa.accept_15_7_12_10_1_4335 7 72 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 160 2 3 36 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 160 (accept_3_3 5 72 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 72 160 4 1 18 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 72 160 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 72
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 72 160 2 1 36 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 160
  (Polychromatic418967fa.accept_7_1_2_6_1_55 1 72 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 72 160)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 160
  (allA_of_3_1 71 71 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 70 160 (allA_succ_of_accept 69 70 160
  (Polychromatic418967fa.accept_21_6_7_13_1_7199 69 70 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 70 160 2 34 35 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 70 160 (Polychromatic418967fa.accept_12_7_10_4_1_382 67 70 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 70 160 2 33 35 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 70 160 5 13 14 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 70 160 2 32 35 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 70 160 (Polychromatic418967fa.accept_17_12_2_7_1_3813
  63 70 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 70 160 2 31 35 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 70 160
  (Polychromatic418967fa.accept_12_1_10_4_1_380 61 70 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 70 160 10 6 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 70 160 (accept_3_3 59 70 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 70
  160 2 29 35 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57
  70 160 (Polychromatic418967fa.accept_11_2_4_6_1_2412 57 70 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 70 160 2 28 35 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 55 70 160 5 11 14 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 54 70 160 2 27 35 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 70 160 (accept_3_3 53 70 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 70 160 2 26 35 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 70 160 (Polychromatic418967fa.accept_13_12_5_4_1_3133 51 70 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 70 160 10 5 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 70 160 (Polychromatic418967fa.accept_12_1_10_4_1_380 49 70 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 70 160 2 24 35 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 70 160 (accept_3_3 47
  70 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 70 160 2 23 35 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 70 160 5 9 14 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 70 160 2 22 35 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 70 160
  (Polychromatic418967fa.accept_12_7_10_4_1_382 43 70 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 70 160 2 21 35 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 70 160 (accept_3_3 41 70 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 70
  160 10 4 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  70 160 (Polychromatic418967fa.accept_19_1_13_8_1_8779 39 70 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 70 160 2 19 35 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 70 160 (Polychromatic418967fa.accept_12_1_10_4_1_380 37 70 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 70 160 2 18 35 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 70 160 5 7 14 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 70 160 2 17 35 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 70 160
  (Polychromatic418967fa.accept_19_14_13_8_1_5943 33 70 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 70 160 2 16 35 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 70 160 (Polychromatic418967fa.accept_12_7_10_4_1_382 31 70 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 70 160 10 3 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 70 160 (accept_3_3 29 70 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 70 160 2 14 35 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 70 160 (Polychromatic418967fa.accept_13_1_5_4_1_463 27 70 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 70 160 2 13 35 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 70 160 5 5 14 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 70 160 2 12 35 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 70 160 (accept_3_3 23 70 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 70 160 2 11 35 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 70 160
  (Polychromatic418967fa.accept_19_2_13_8_1_8778 21 70 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 70 160 10 2 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 70 160 (Polychromatic418967fa.accept_12_7_10_4_1_382 19 70 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 70 160 2 9 35 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 70 160 (accept_3_3 17 70 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 70 160 2 8 35 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 70 160 5 3 14 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 70 160 2 7 35 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 70 160 (Polychromatic418967fa.accept_11_2_4_6_1_2412 13 70 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 70 160 2 6 35 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 70 160 (accept_3_3 11 70 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70 160 10 1 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 70 160 (Polychromatic418967fa.accept_13_9_5_4_1_1591 9 70 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 70 160 2 4 35 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 70 160
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 70 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 70 160 2 3 35 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 70 160 5 1 14 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 70 160 2 2 35 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 70 160 (Polychromatic418967fa.accept_19_3_13_8_1_4476 3 70 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 70 160 2 1 35 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 70 160 (Polychromatic418967fa.accept_12_1_10_4_1_380 1 70 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70
  160)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 160 (allA_succ_of_accept 68 69
  160 (accept_3_3 68 69 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 69 160
  (Polychromatic418967fa.accept_6_1_3_4_1_1 67 69 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 69 160 (Polychromatic418967fa.accept_9_3_6_7_1_562 66 69 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 69 160 (accept_3_3 65 69 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 69 160 (Polychromatic418967fa.accept_9_1_6_7_1_285 64 69 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 160 (Polychromatic418967fa.accept_11_8_3_6_1_1855
  63 69 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 160 (accept_3_3 62
  69 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 160
  (Polychromatic418967fa.accept_6_1_3_4_1_1 61 69 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 69 160 (Polychromatic418967fa.accept_18_6_15_16_1_7325 60 69 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 69 160 (accept_3_3 59 69 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 69 160 (Polychromatic418967fa.accept_9_4_6_7_1_286 58 69 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 160 (Polychromatic418967fa.accept_9_3_6_7_1_562 57
  69 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 160 (accept_3_3 56 69
  160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 69 160 (Polychromatic418967fa.accept_6_1_3_4_1_1
  55 69 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 69 160
  (Polychromatic418967fa.accept_12_6_9_4_1_96 54 69 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 69 160 (accept_3_3 53 69 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  69 160 (Polychromatic418967fa.accept_11_8_3_6_1_1855 52 69 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 69 160 (Polychromatic418967fa.accept_21_9_6_13_1_8777 51 69 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 160 (accept_3_3 50 69 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 69 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 69 160
  (Polychromatic418967fa.accept_9_3_6_7_1_562 48 69 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 69 160 (accept_3_3 47 69 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  69 160 (Polychromatic418967fa.accept_9_1_6_7_1_285 46 69 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 69 160 (Polychromatic418967fa.accept_17_11_1_7_1_2657 45 69 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 160 (accept_3_3 44 69 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 69 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 69 160
  (Polychromatic418967fa.accept_11_9_3_6_1_797 42 69 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 69 160 (accept_3_3 41 69 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  69 160 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 69 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 69 160 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 69 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 160 (accept_3_3 38 69 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 69 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 69 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 69 160
  (Polychromatic418967fa.accept_21_15_6_13_1_8776 36 69 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 69 160 (accept_3_3 35 69 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  69 160 (Polychromatic418967fa.accept_15_4_9_10_1_5384 34 69 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 69 160 (Polychromatic418967fa.accept_14_5_13_6_1_3574 33 69 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 160 (accept_3_3 32 69 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 69 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 69 160
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 69 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 69 160 (accept_3_3 29 69 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  69 160 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 69 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 69 160 (Polychromatic418967fa.accept_15_12_9_10_1_2326 27 69 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 160 (accept_3_3 26 69 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 69 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 69 160
  (Polychromatic418967fa.accept_18_6_15_16_1_7325 24 69 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 69 160 (accept_3_3 23 69 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  69 160 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 69 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 69 160 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 69 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 160 (accept_3_3 20 69 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 69 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 69 160
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 69 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 69 160 (accept_3_3 17 69 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  69 160 (Polychromatic418967fa.accept_15_1_9_10_1_2327 16 69 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 69 160 (Polychromatic418967fa.accept_19_15_12_8_1_5922 15 69 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 160 (accept_3_3 14 69 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 69 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 69 160
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 69 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 69 160 (accept_3_3 11 69 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  69 160 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 69 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 69 160 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 69 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 160 (accept_3_3 8 69 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 69 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69 160
  (Polychromatic418967fa.accept_12_6_9_4_1_96 6 69 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 160 (accept_3_3 5 69 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69
  160 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 69 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 69 160 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 69 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 160 (accept_3_3 2 69 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 69 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 69 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  160))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 160 (allA_of_3_1 68 68 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 67 160 (allA_succ_of_accept 66 67 160
  (Polychromatic418967fa.accept_7_3_4_6_1_329 66 67 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 160 (accept_3_3 65 67 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 67 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 67 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 160 (accept_3_3 62 67 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 160 (Polychromatic418967fa.accept_7_5_4_6_1_167 61 67 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 160
  (Polychromatic418967fa.accept_9_6_4_7_1_300 60 67 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 160 (accept_3_3 59 67 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 160 (Polychromatic418967fa.accept_7_2_4_6_1_166 58 67 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 67 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 160 (accept_3_3 56 67 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 67 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 160
  (Polychromatic418967fa.accept_7_5_4_6_1_167 54 67 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 160 (accept_3_3 53 67 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 160 (Polychromatic418967fa.accept_7_3_4_6_1_329 52 67 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 67 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 160 (accept_3_3 50 67 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 160 (Polychromatic418967fa.accept_11_5_1_6_1_774 49 67 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 160
  (Polychromatic418967fa.accept_9_3_4_7_1_89 48 67 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 160 (accept_3_3 47 67 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 67 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 67 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 160 (accept_3_3 44 67 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 160 (Polychromatic418967fa.accept_19_5_10_8_1_8775 43 67 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 160
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 67 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 160 (accept_3_3 41 67 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 160 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 67 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 67 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 160 (accept_3_3 38 67 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 160 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 67 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 160
  (Polychromatic418967fa.accept_19_17_10_8_1_5942 36 67 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 160 (accept_3_3 35 67 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 160 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 67 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 67 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 160 (accept_3_3 32 67 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 160 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 67 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 160
  (Polychromatic418967fa.accept_7_2_4_6_1_166 30 67 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 160 (accept_3_3 29 67 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 67 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 67 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 160 (accept_3_3 26 67 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 160 (Polychromatic418967fa.accept_13_12_2_4_1_3131 25 67 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 160
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 67 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 160 (accept_3_3 23 67 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 160 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 67 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 67 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 160 (accept_3_3 20 67 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 160 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 67 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 160
  (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 67 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 160 (accept_3_3 17 67 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 160 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 67 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 67 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 160 (accept_3_3 14 67 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 160 (Polychromatic418967fa.accept_29_13_9_15_1_8774 13 67 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 160
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 67 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 160 (accept_3_3 11 67 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 160 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 67 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 67 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 160 (accept_3_3 8 67 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 160 (Polychromatic418967fa.accept_11_7_1_6_1_1281 7 67 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 160
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 67 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 160 (accept_3_3 5 67 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  160 (Polychromatic418967fa.accept_15_4_7_10_1_807 4 67 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 67 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 67 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 160 (accept_3_3 2 67 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 67 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  160))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 160 (allA_succ_of_accept 65 66
  160 (accept_3_3 65 66 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 66 160 2 32 33 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 66 160
  (Polychromatic418967fa.accept_12_3_6_4_1_400 63 66 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 66 160 2 31 33 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 66 160 (Polychromatic418967fa.accept_15_1_6_10_1_23 61 66 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 160 2 30 33 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 160 (accept_3_3 59 66 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 58 66 160 2 29 33 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 66 160 (Polychromatic418967fa.accept_12_9_6_4_1_402 57 66 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 66 160 2 28 33 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 66 160
  (Polychromatic418967fa.accept_9_1_3_7_1_6 55 66 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 66 160 2 27 33 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 66 160 (accept_3_3 53 66 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 66
  160 2 26 33 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  66 160 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 66 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 66 160 2 25 33 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 66 160 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 66 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 160 2 24 33 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 160 (accept_3_3 47 66 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 66 160 2 23 33 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 66 160
  (Polychromatic418967fa.accept_12_9_6_4_1_402 45 66 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 66 160 2 22 33 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 66 160 (Polychromatic418967fa.accept_17_9_15_7_1_6212 43 66 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 66 160 2 21 33 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 66 160 (accept_3_3 41 66 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 66 160 2 20 33 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 66 160 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 66 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 66 160 2 19 33 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 66 160
  (Polychromatic418967fa.accept_7_2_3_6_1_4 37 66 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 66 160 2 18 33 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 66 160 (accept_3_3 35 66 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 66
  160 2 17 33 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  66 160 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 66 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 66 160 2 16 33 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 66 160 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 66 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 160 2 15 33 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 160 (accept_3_3 29 66 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 66 160 2 14 33 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 66 160
  (Polychromatic418967fa.accept_12_3_6_4_1_400 27 66 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 66 160 2 13 33 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 66 160 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 66 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 160 2 12 33 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 160 (accept_3_3 23 66 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 160 2 11 33 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 66 160 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 66 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 66 160 2 10 33 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 66 160
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 66 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 66 160 2 9 33 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 66 160 (accept_3_3 17 66 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66
  160 2 8 33 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  66 160 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 66 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 66 160 2 7 33 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 66 160 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 66 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 160 2 6 33 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 160 (accept_3_3 11 66 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 66 160 2 5 33 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 66 160 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 66 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 66 160 2 4 33 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 66 160
  (Polychromatic418967fa.accept_19_7_9_8_1_7297 7 66 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 66 160 2 3 33 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 66 160 (accept_3_3 5 66 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 160
  2 2 33 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 66
  160 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 66 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 66 160 2 1 33 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 66 160 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 66 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 66 160))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 65 160 (allA_of_3_1 65 65 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 64 160
  (allA_succ_of_accept 63 64 160 (Polychromatic418967fa.accept_13_11_12_4_1_3945 63 64 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 64 160 2 31 32 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 64 160 (Polychromatic418967fa.accept_7_5_1_6_1_163 61
  64 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 64 160 4 15 16 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 64 160 (accept_3_3 59
  64 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 64 160 2 29 32 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 64 160
  (Polychromatic418967fa.accept_9_3_1_7_1_97 57 64 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 64 160 8 7 8 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 64 160 (Polychromatic418967fa.accept_13_3_12_4_1_110 55 64 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 64 160 2 27 32 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 64 160 (accept_3_3 53 64 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 64 160 4 13 16 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 64 160 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 64 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 64 160 2 25 32 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 64 160
  (Polychromatic418967fa.accept_9_4_1_7_1_293 49 64 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 64 160 16 3 4 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 64 160 (accept_3_3 47 64 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 64
  160 2 23 32 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  64 160 (Polychromatic418967fa.accept_17_11_13_7_1_3795 45 64 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 64 160 4 11 16 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 64 160 (Polychromatic418967fa.accept_15_13_4_10_1_821 43 64 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 64 160 2 21 32 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 64 160 (accept_3_3 41 64 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 64 160 8 5 8 20 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 64 160 (Polychromatic418967fa.accept_9_3_1_7_1_97 39
  64 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 64 160 2 19 32 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 64 160
  (Polychromatic418967fa.accept_7_2_1_6_1_173 37 64 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 64 160 4 9 16 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 64 160 (accept_3_3 35 64 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 64
  160 2 17 32 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  64 160 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 64 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 64 160 32 1 2 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 64 160 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 64 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 64 160 2 15 32 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 64 160 (accept_3_3 29 64 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 64 160 4 7 16 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 64 160 (Polychromatic418967fa.accept_23_4_18_22_1_8773 27 64
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 64 160 2 13 32 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 64 160
  (Polychromatic418967fa.accept_11_3_9_6_1_105 25 64 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 64 160 8 3 8 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 64 160 (accept_3_3 23 64 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 64
  160 2 11 32 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  64 160 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 64 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 64 160 4 5 16 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 64 160 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 64 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 64 160 2 9 32 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 64 160 (accept_3_3 17 64 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 64 160 16 1 4 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 64 160 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 64 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 64 160 2 7 32 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 64 160
  (Polychromatic418967fa.accept_9_4_1_7_1_293 13 64 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 64 160 4 3 16 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 64 160 (accept_3_3 11 64 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 64
  160 2 5 32 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  64 160 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 64 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 64 160 8 1 8 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 64 160 (Polychromatic418967fa.accept_13_7_12_4_1_450 7 64 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 64 160 2 3 32 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 64 160 (accept_3_3 5 64 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 64 160 4 1 16 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 64 160 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 64 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 64 160 2 1 32 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 64 160
  (Polychromatic418967fa.accept_18_1_10_16_1_566 1 64 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 64 160)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 160
  (allA_succ_of_accept 62 63 160 (accept_3_3 62 63 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  63 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 63 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 63 160 (Polychromatic418967fa.accept_13_8_11_4_1_1553 60 63 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 63 160 (accept_3_3 59 63 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 160 (Polychromatic418967fa.accept_11_3_8_6_1_788 58 63 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 160
  (Polychromatic418967fa.accept_14_1_7_6_1_3604 57 63 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 63 160 (accept_3_3 56 63 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  63 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 63 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 63 160 (Polychromatic418967fa.accept_12_6_3_4_1_394 54 63 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 63 160 (accept_3_3 53 63 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 160 (Polychromatic418967fa.accept_15_7_3_10_1_817 52 63 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 160
  (Polychromatic418967fa.accept_13_12_11_4_1_3111 51 63 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 63 160 (accept_3_3 50 63 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  63 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 63 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 63 160 (Polychromatic418967fa.accept_18_12_9_16_1_4732 48 63 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 63 160 (accept_3_3 47 63 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 160 (Polychromatic418967fa.accept_13_7_11_4_1_2247 46 63
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 160
  (Polychromatic418967fa.accept_13_6_11_4_1_938 45 63 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 63 160 (accept_3_3 44 63 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  63 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 63 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 63 160 (Polychromatic418967fa.accept_12_6_3_4_1_394 42 63 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 63 160 (accept_3_3 41 63 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 160 (Polychromatic418967fa.accept_19_2_6_8_1_3284 40 63 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 160
  (Polychromatic418967fa.accept_15_9_3_10_1_2312 39 63 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 63 160 (accept_3_3 38 63 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  63 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 63 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 63 160 (Polychromatic418967fa.accept_11_3_8_6_1_788 36 63 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 63 160 (accept_3_3 35 63 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 160 (Polychromatic418967fa.accept_13_8_11_4_1_1553 34 63 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 160
  (Polychromatic418967fa.accept_13_7_11_4_1_2247 33 63 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 63 160 (accept_3_3 32 63 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  63 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 63 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 63 160 (Polychromatic418967fa.accept_12_6_3_4_1_394 30 63 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 160 (accept_3_3 29 63 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 160 (Polychromatic418967fa.accept_13_2_11_4_1_445 28 63 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 160
  (Polychromatic418967fa.accept_14_13_7_6_1_3525 27 63 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 63 160 (accept_3_3 26 63 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  63 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 63 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 63 160 (Polychromatic418967fa.accept_15_9_3_10_1_2312 24 63 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 160 (accept_3_3 23 63 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 160 (Polychromatic418967fa.accept_14_8_7_6_1_1159 22 63 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 160
  (Polychromatic418967fa.accept_13_8_11_4_1_1553 21 63 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 63 160 (accept_3_3 20 63 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  63 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 63 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 63 160 (Polychromatic418967fa.accept_12_6_3_4_1_394 18 63 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 160 (accept_3_3 17 63 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 160 (Polychromatic418967fa.accept_19_16_6_8_1_8772 16 63 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 160
  (Polychromatic418967fa.accept_13_2_11_4_1_445 15 63 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 63 160 (accept_3_3 14 63 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  63 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 63 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 63 160 (Polychromatic418967fa.accept_13_12_11_4_1_3111 12 63 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 160 (accept_3_3 11 63 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 160 (Polychromatic418967fa.accept_13_10_11_4_1_2248 10 63
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 160
  (Polychromatic418967fa.accept_15_9_3_10_1_2312 9 63 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 63 160 (accept_3_3 8 63 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63
  160 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 63 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 63 160 (Polychromatic418967fa.accept_12_6_3_4_1_394 6 63 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 160 (accept_3_3 5 63 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 63 160 (Polychromatic418967fa.accept_17_4_12_7_1_8771 4 63 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 160 (Polychromatic418967fa.accept_11_3_8_6_1_788 3
  63 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 160 (accept_3_3 2 63 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 63
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  160))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 160 (allA_of_3_1 62 62 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 61 160 (allA_succ_of_accept 60 61 160
  (Polychromatic418967fa.accept_7_4_5_6_1_344 60 61 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 160 (accept_3_3 59 61 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 160 (Polychromatic418967fa.accept_12_10_1_4_1_392 58 61 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 61 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 160 (accept_3_3 56 61 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 160 (Polychromatic418967fa.accept_14_13_5_6_1_2747 55 61 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 160
  (Polychromatic418967fa.accept_15_9_1_10_1_4316 54 61 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 160 (accept_3_3 53 61 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 160 (Polychromatic418967fa.accept_15_7_1_10_1_305 52 61 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 61 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 160 (accept_3_3 50 61 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 160 (Polychromatic418967fa.accept_21_7_19_13_1_7164 49 61 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 160
  (Polychromatic418967fa.accept_17_14_10_7_1_2670 48 61 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 160 (accept_3_3 47 61 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 160 (Polychromatic418967fa.accept_7_4_5_6_1_344 46 61 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 61 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 160 (accept_3_3 44 61 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 160 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 61 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 160
  (Polychromatic418967fa.accept_23_19_15_22_1_8770 42 61 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 61 160 (accept_3_3 41 61 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 61 160 (Polychromatic418967fa.accept_18_4_7_16_1_2307 40 61 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 61 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 61 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 160 (accept_3_3 38 61 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 160 (Polychromatic418967fa.accept_15_7_1_10_1_305
  37 61 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 160
  (Polychromatic418967fa.accept_7_1_5_6_1_59 36 61 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 160 (accept_3_3 35 61 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 160 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 61 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 61 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 160 (accept_3_3 32 61 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 160 (Polychromatic418967fa.accept_13_5_9_4_1_441 31 61 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 160
  (Polychromatic418967fa.accept_22_8_17_6_1_8769 30 61 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 160 (accept_3_3 29 61 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 160 (Polychromatic418967fa.accept_15_13_1_10_1_816 28 61 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 61 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 160 (accept_3_3 26 61 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 160 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 61 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 160
  (Polychromatic418967fa.accept_15_9_1_10_1_4316 24 61 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 160 (accept_3_3 23 61 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 160 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 61 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 61 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 160 (accept_3_3 20 61 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 160 (Polychromatic418967fa.accept_13_6_9_4_1_2288 19 61 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 160
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 61 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 160 (accept_3_3 17 61 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 160 (Polychromatic418967fa.accept_17_16_10_7_1_2671 16 61 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 61 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 160 (accept_3_3 14 61 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 160 (Polychromatic418967fa.accept_14_13_5_6_1_2747 13 61 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 160
  (Polychromatic418967fa.accept_19_12_4_8_1_8768 12 61 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 160 (accept_3_3 11 61 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 160 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 61 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 61 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 160 (accept_3_3 8 61 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 160 (Polychromatic418967fa.accept_13_7_9_4_1_918 7 61 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 160
  (Polychromatic418967fa.accept_13_6_9_4_1_2288 6 61 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 160 (accept_3_3 5 61 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  160 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 61 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 61 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 160 (accept_3_3 2 61 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 160 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 61 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 160)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 160 (allA_succ_of_accept 59 60 160 (accept_3_3 59 60 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 60 160 2 29 30 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 60 160 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 60 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 60 160 4 14 15 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 60 160 5 11 12 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 60 160 2 27 30 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 160 (accept_3_3 53 60 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 60 160 4 13 15 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 60 160 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 60 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 60 160 10 5 6 16 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 60 160
  (Polychromatic418967fa.accept_9_4_6_7_1_286 49 60 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 60 160 4 12 15 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 60 160 (accept_3_3 47 60 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 60
  160 2 23 30 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 60
  160 5 9 12 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 60
  160 4 11 15 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43
  60 160 (Polychromatic418967fa.accept_11_10_5_6_1_1842 43 60 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 60 160 2 21 30 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 60 160 (accept_3_3 41 60 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 60 160 20 2 3 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 60 160 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 60 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 60 160 2 19 30 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 60 160 (Polychromatic418967fa.accept_7_2_4_6_1_166 37
  60 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 160 4 9 15 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 60 160 5 7 12 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 60 160 2 17 30 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 60 160
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 60 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 60 160 4 8 15 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 60 160 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 60 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60 160 10 3 6 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 60 160 (accept_3_3 29 60 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 60 160 4 7 15 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 60 160 (Polychromatic418967fa.accept_21_6_18_13_1_8767 27 60 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 60 160 2 13 30 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 60 160 5 5 12 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 60 160 4 6 15 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 160 (accept_3_3 23 60 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 160 2 11 30 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 60 160
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 60 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 60 160 20 1 3 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 60 160 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 60 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 160 2 9 30 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 60 160 (accept_3_3 17 60 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 60 160 4 4 15 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 60 160 5 3 12 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 60 160 2 7 30 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 60 160 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 60 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 160 4 3 15 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 160 (accept_3_3 11 60 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 160 10 1 6 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 60 160 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 60 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 60 160 4 2 15 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 60 160
  (Polychromatic418967fa.accept_21_7_18_13_1_5585 7 60 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 60 160 2 3 30 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 60 160 5 1 12 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 60 160 4 1 15 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 60 160 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 60 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 60 160 2 1 30 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 160 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 60 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  160)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 160 (allA_of_3_1 59 59 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 58 160 (allA_succ_of_accept 57 58 160
  (Polychromatic418967fa.accept_7_1_2_6_1_55 57 58 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 58 160 2 28 29 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 58 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 58 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 58 160 2 27 29 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 58 160 (accept_3_3 53 58 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 58 160 2 26 29 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 58 160 (Polychromatic418967fa.accept_9_6_4_7_1_300 51 58 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 58 160 2 25 29 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 58 160
  (Polychromatic418967fa.accept_12_1_10_4_1_380 49 58 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 58 160 2 24 29 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 58 160 (accept_3_3 47 58 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 58
  160 2 23 29 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  58 160 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 58 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 58 160 2 22 29 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 58 160 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 58 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 58 160 2 21 29 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 58 160 (accept_3_3 41 58 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 58 160 2 20 29 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 58 160
  (Polychromatic418967fa.accept_7_4_2_6_1_337 39 58 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 58 160 2 19 29 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 58 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 58 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 58 160 2 18 29 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 58 160 (accept_3_3 35 58 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 58 160 2 17 29 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 58 160 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 58 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 58 160 2 16 29 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 58 160
  (Polychromatic418967fa.accept_7_3_2_6_1_56 31 58 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 58 160 2 15 29 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 58 160 (accept_3_3 29 58 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 58
  160 2 14 29 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  58 160 (Polychromatic418967fa.accept_15_12_13_10_1_812 27 58 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 58 160 2 13 29 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 58 160 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 58 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 58 160 2 12 29 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 58 160 (accept_3_3 23 58 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 58 160 2 11 29 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 58 160
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 58 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 58 160 2 10 29 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 58 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 58 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 58 160 2 9 29 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 58 160 (accept_3_3 17 58 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 58 160 2 8 29 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 58 160 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 58 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 58 160 2 7 29 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 58 160 (Polychromatic418967fa.accept_12_1_10_4_1_380
  13 58 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 58 160 2 6 29 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 58 160 (accept_3_3 11
  58 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 58 160 2 5 29 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 58 160
  (Polychromatic418967fa.accept_11_9_3_6_1_797 9 58 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 58 160 2 4 29 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 58 160 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 58 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 58 160 2 3 29 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 58 160 (accept_3_3 5 58 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 58 160 2 2 29 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 58 160 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 58 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 58 160 2 1 29 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 58 160 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 58
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  160)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 160 (allA_succ_of_accept 56 57 160
  (accept_3_3 56 57 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 160
  (Polychromatic418967fa.accept_6_1_3_4_1_1 55 57 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 57 160 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 57 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 160 (accept_3_3 53 57 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 57 160 (Polychromatic418967fa.accept_15_7_12_10_1_4335 52 57 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 160
  (Polychromatic418967fa.accept_7_2_1_6_1_173 51 57 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 57 160 (accept_3_3 50 57 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  57 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 57 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 57 160 (Polychromatic418967fa.accept_11_4_2_6_1_389 48 57 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 57 160 (accept_3_3 47 57 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 160 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 57 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 160
  (Polychromatic418967fa.accept_13_6_5_4_1_3924 45 57 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 57 160 (accept_3_3 44 57 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  57 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 57 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 57 160 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 57 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 57 160 (accept_3_3 41 57 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 160 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 57 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 160
  (Polychromatic418967fa.accept_15_9_12_10_1_809 39 57 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 57 160 (accept_3_3 38 57 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  57 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 57 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 57 160 (Polychromatic418967fa.accept_13_10_5_4_1_3107 36 57 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 57 160 (accept_3_3 35 57 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 160 (Polychromatic418967fa.accept_25_9_7_10_1_6850 34 57
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 160
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 57 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 57 160 (accept_3_3 32 57 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  57 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 57 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 57 160 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 57 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 57 160 (accept_3_3 29 57 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 160 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 57 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 160
  (Polychromatic418967fa.accept_13_1_5_4_1_463 27 57 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 57 160 (accept_3_3 26 57 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  57 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 57 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 57 160 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 57 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 57 160 (accept_3_3 23 57 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 160 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 57 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 160
  (Polychromatic418967fa.accept_14_7_1_6_1_3514 21 57 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 57 160 (accept_3_3 20 57 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  57 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 57 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 57 160 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 57 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 57 160 (accept_3_3 17 57 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 160 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 57 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 160
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 57 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 57 160 (accept_3_3 14 57 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  57 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 57 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 57 160 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 57 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 57 160 (accept_3_3 11 57 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 160 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 57 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 160
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 57 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 57 160 (accept_3_3 8 57 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57
  160 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 57 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 57 160 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 57 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 57 160 (accept_3_3 5 57 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 57 160 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 57 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 57 160 (Polychromatic418967fa.accept_23_3_11_22_1_8766
  3 57 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 160 (accept_3_3 2 57
  160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  57 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57
  160))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 56 160 (allA_of_3_1 56 56 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 55 160 (allA_succ_of_accept 54 55 160
  (Polychromatic418967fa.accept_14_12_13_6_1_1140 54 55 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 55 160 (accept_3_3 53 55 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  55 160 (Polychromatic418967fa.accept_25_2_5_10_1_8765 52 55 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 55 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 55 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 55 160 5 10 11 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 55 160
  (Polychromatic418967fa.accept_9_4_1_7_1_293 49 55 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 55 160 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 55 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 160 (accept_3_3 47 55 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 55 160 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 55 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 55 160 5 9 11 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 55 160 (accept_3_3 44 55 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 160 (Polychromatic418967fa.accept_18_7_1_16_1_578 43 55 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 160
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 55 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 160 (accept_3_3 41 55 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 55
  160 5 8 11 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  55 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 55 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 55 160 (accept_3_3 38 55 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 55 160 (Polychromatic418967fa.accept_17_3_4_7_1_1658 37 55 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 160 (Polychromatic418967fa.accept_23_13_9_22_1_8764 36 55
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 55 160 5 7 11 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 55 160
  (Polychromatic418967fa.accept_12_10_7_4_1_820 34 55 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 55 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 55 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 160 (accept_3_3 32 55 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 55 160 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 55 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 55 160 5 6 11 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 55 160 (accept_3_3 29 55 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 160 (Polychromatic418967fa.accept_18_10_1_16_1_579 28 55 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 55 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 55 160 (accept_3_3 26 55 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 55
  160 5 5 11 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24
  55 160 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 55 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 55 160 (accept_3_3 23 55 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 55 160 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 55 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 55 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 55 160 5 4 11 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 55 160
  (Polychromatic418967fa.accept_14_5_13_6_1_3574 19 55 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 55 160 (Polychromatic418967fa.accept_22_18_11_6_1_8763 18 55 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 160 (accept_3_3 17 55 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 55 160 (Polychromatic418967fa.accept_19_16_17_8_1_8762 16 55 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 55 160 5 3 11 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 55 160 (accept_3_3 14 55 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 160 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 55 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 160
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 55 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 160 (accept_3_3 11 55 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 55
  160 5 2 11 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  55 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 55 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 55 160 (accept_3_3 8 55 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 55 160 (Polychromatic418967fa.accept_13_7_3_4_1_459 7 55 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 160 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 55 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 55 160 5 1 11 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 55 160
  (Polychromatic418967fa.accept_9_4_1_7_1_293 4 55 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 55 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 160 (accept_3_3 2 55 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 160 (Polychromatic418967fa.accept_13_1_3_4_1_925 1 55 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 160)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 54 160 (allA_succ_of_accept 53 54 160 (accept_3_3 53 54 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 54 160 2 26 27 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 54 160 (Polychromatic418967fa.accept_12_3_6_4_1_400 51 54 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 54 160 2 25 27 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 54 160 (Polychromatic418967fa.accept_11_5_10_6_1_793
  49 54 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 160 2 24 27 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 160 (accept_3_3 47
  54 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 54 160 2 23 27 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 54 160
  (Polychromatic418967fa.accept_12_9_6_4_1_402 45 54 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 54 160 2 22 27 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 54 160 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 54 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54 160 2 21 27 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 54 160 (accept_3_3 41 54 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 54 160 2 20 27 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 54 160 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 54 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 54 160 2 19 27 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 54 160
  (Polychromatic418967fa.accept_13_11_2_4_1_1590 37 54 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 54 160 2 18 27 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 54 160 (accept_3_3 35 54 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 54
  160 2 17 27 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  54 160 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 54 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 54 160 2 16 27 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 54 160 (Polychromatic418967fa.accept_13_5_2_4_1_3955 31 54 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 160 2 15 27 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 160 (accept_3_3 29 54 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 160 2 14 27 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 54 160
  (Polychromatic418967fa.accept_11_5_10_6_1_793 27 54 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 54 160 2 13 27 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 54 160 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 54 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54 160 2 12 27 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 54 160 (accept_3_3 23 54 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 54 160 2 11 27 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 54 160 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 54 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 54 160 2 10 27 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 54 160
  (Polychromatic418967fa.accept_13_6_2_4_1_923 19 54 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 54 160 2 9 27 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 54 160 (accept_3_3 17 54 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54
  160 2 8 27 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  54 160 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 54 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 54 160 2 7 27 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 54 160 (Polychromatic418967fa.accept_14_13_12_6_1_2735 13 54 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 160 2 6 27 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 160 (accept_3_3 11 54 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 54 160 2 5 27 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 54 160 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 54 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 54 160 2 4 27 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 160
  (Polychromatic418967fa.accept_19_7_16_8_1_8761 7 54 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 54 160 2 3 27 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 54 160 (accept_3_3 5 54 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 160
  2 2 27 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 54
  160 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 54 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 54 160 2 1 27 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 54 160 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 54 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 54 160)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53
  160 (allA_of_3_1 53 53 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 52 160 (allA_succ_of_accept 51 52 160
  (Polychromatic418967fa.accept_7_2_3_6_1_4 51 52 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 52 160 2 25 26 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 52 160 (Polychromatic418967fa.accept_15_4_7_10_1_807 49 52 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 52 160 4 12 13 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 52 160 (accept_3_3 47 52 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 52 160 2 23 26 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 52 160 (Polychromatic418967fa.accept_14_3_10_6_1_1136 45 52 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 52 160 4 11 13 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 52 160
  (Polychromatic418967fa.accept_19_5_14_8_1_5944 43 52 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 52 160 2 21 26 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 52 160 (accept_3_3 41 52 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 52
  160 4 10 13 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  52 160 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 52 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 52 160 2 19 26 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 52 160 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 52 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 52 160 4 9 13 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 52 160 (accept_3_3 35 52 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 52 160 2 17 26 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 52 160 (Polychromatic418967fa.accept_15_3_7_10_1_2324
  33 52 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 52 160 4 8 13 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 52 160
  (Polychromatic418967fa.accept_14_3_10_6_1_1136 31 52 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 52 160 2 15 26 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 52 160 (accept_3_3 29 52 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 52
  160 4 7 13 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  52 160 (Polychromatic418967fa.accept_15_12_7_10_1_3297 27 52 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 52 160 2 13 26 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 52 160 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 52 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 52 160 4 6 13 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 52 160 (accept_3_3 23 52 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 52 160 2 11 26 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 52 160 (Polychromatic418967fa.accept_19_2_14_8_1_3273
  21 52 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 52 160 4 5 13 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 52 160
  (Polychromatic418967fa.accept_15_4_7_10_1_807 19 52 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 52 160 2 9 26 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 52 160 (accept_3_3 17 52 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 52
  160 4 4 13 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  52 160 (Polychromatic418967fa.accept_22_15_8_6_1_8760 15 52 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 52 160 2 7 26 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 52 160 (Polychromatic418967fa.accept_19_13_14_8_1_4490 13 52 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 52 160 4 3 13 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 52 160 (accept_3_3 11 52 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 52 160 2 5 26 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 52 160 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 52 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 52 160 4 2 13 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 52 160
  (Polychromatic418967fa.accept_19_7_14_8_1_4535 7 52 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 52 160 2 3 26 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 52 160 (accept_3_3 5 52 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 52 160
  4 1 13 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 52
  160 (Polychromatic418967fa.accept_11_3_8_6_1_788 3 52 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 52 160 2 1 26 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 52 160 (Polychromatic418967fa.accept_15_1_7_10_1_287 1 52 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 52 160)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 160
  (allA_succ_of_accept 50 51 160 (accept_3_3 50 51 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  51 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 51 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 51 160 (Polychromatic418967fa.accept_9_3_6_7_1_562 48 51 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 160 (accept_3_3 47 51 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 160 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 51 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 160
  (Polychromatic418967fa.accept_7_3_2_6_1_56 45 51 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 51 160 (accept_3_3 44 51 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  51 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 51 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 51 160 (Polychromatic418967fa.accept_12_6_3_4_1_394 42 51 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 160 (accept_3_3 41 51 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 160 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 51 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 160
  (Polychromatic418967fa.accept_7_4_2_6_1_337 39 51 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 51 160 (accept_3_3 38 51 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  51 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 51 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 51 160 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 51 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 51 160 (accept_3_3 35 51 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 160 (Polychromatic418967fa.accept_11_1_7_6_1_378 34 51 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 160
  (Polychromatic418967fa.accept_13_7_12_4_1_450 33 51 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 51 160 (accept_3_3 32 51 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  51 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 51 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 51 160 (Polychromatic418967fa.accept_9_3_6_7_1_562 30 51 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 160 (accept_3_3 29 51 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 160 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 51 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 160
  (Polychromatic418967fa.accept_15_12_6_10_1_1516 27 51 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 51 160 (accept_3_3 26 51 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  51 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 51 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 51 160 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 51 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 51 160 (accept_3_3 23 51 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 160 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 51 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 160
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 51 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 51 160 (accept_3_3 20 51 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  51 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 51 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 51 160 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 51 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 51 160 (accept_3_3 17 51 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 160 (Polychromatic418967fa.accept_13_3_12_4_1_110 16 51 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 160
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 51 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 51 160 (accept_3_3 14 51 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  51 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 51 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 51 160 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 51 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 160 (accept_3_3 11 51 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 160 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 51 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 160
  (Polychromatic418967fa.accept_18_9_15_16_1_8759 9 51 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 51 160 (accept_3_3 8 51 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51
  160 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 51 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 51 160 (Polychromatic418967fa.accept_12_6_3_4_1_394 6 51 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 51 160 (accept_3_3 5 51 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 51 160 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 51 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 51 160 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 51
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 160 (accept_3_3 2 51 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 51
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51
  160))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 160 (allA_of_3_1 50 50 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 49 160 (allA_succ_of_accept 48 49 160 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 49
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 160 (accept_3_3 47 49 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 49 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 46
  49 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 49 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 49 160 (accept_3_3 44 49 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  49 160 (Polychromatic418967fa.accept_11_10_5_6_1_1842 43 49 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 49 160 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 49 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 49 160 (accept_3_3 41 49 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 49 160 (Polychromatic418967fa.accept_13_1_10_4_1_954 40 49 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 49 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 49 160 (accept_3_3 38 49 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  49 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 49 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 49 160 (Polychromatic418967fa.accept_14_8_7_6_1_1159 36 49 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 49 160 (accept_3_3 35 49 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 49 160 (Polychromatic418967fa.accept_11_1_5_6_1_397 34 49 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 49 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 49 160 (accept_3_3 32 49 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  49 160 (Polychromatic418967fa.accept_13_5_10_4_1_1564 31 49 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 49 160 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 49 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 160 (accept_3_3 29 49 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 49 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 49 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 49 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 49 160 (accept_3_3 26 49 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  49 160 (Polychromatic418967fa.accept_21_4_7_13_1_8757 25 49 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 49 160 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 49 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 160 (accept_3_3 23 49 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 160 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 49 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 49 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 49 160 (accept_3_3 20 49 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  49 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 49 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 49 160 (Polychromatic418967fa.accept_13_5_10_4_1_1564 18 49 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 160 (accept_3_3 17 49 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 49 160 (Polychromatic418967fa.accept_19_16_11_8_1_8758 16 49
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 49 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 49 160 (accept_3_3 14 49 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  49 160 (Polychromatic418967fa.accept_14_13_7_6_1_3525 13 49 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 49 160 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 49 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 160 (accept_3_3 11 49 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 49 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 49 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 160 (accept_3_3 8 49 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49
  160 (Polychromatic418967fa.accept_13_7_10_4_1_919 7 49 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 49 160 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 49 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 160 (accept_3_3 5 49 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 49 160 (Polychromatic418967fa.accept_21_4_7_13_1_8757 4 49 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 49 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 49 160 (accept_3_3 2 49 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49
  160 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 49 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 49 160))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 48 160 (allA_succ_of_accept 47 48 160
  (accept_3_3 47 48 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 48 160 2 23 24 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 48 160
  (Polychromatic418967fa.accept_13_6_9_4_1_2288 45 48 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 48 160 4 11 12 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 48 160 (Polychromatic418967fa.accept_15_13_3_10_1_2296 43 48 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 160 2 21 24 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 160 (accept_3_3 41 48 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 48 160 8 5 6 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 48 160 (Polychromatic418967fa.accept_15_9_3_10_1_2312 39 48 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 48 160 2 19 24 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 160
  (Polychromatic418967fa.accept_9_1_3_7_1_6 37 48 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 48 160 4 9 12 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 48 160 (accept_3_3 35 48 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48
  160 2 17 24 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  48 160 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 48 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 48 160 16 2 3 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 48 160 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 48 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 160 2 15 24 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 160 (accept_3_3 29 48 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 48 160 4 7 12 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 48 160 (Polychromatic418967fa.accept_17_10_14_7_1_2679 27 48
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 48 160 2 13 24 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 48 160
  (Polychromatic418967fa.accept_17_8_14_7_1_6203 25 48 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 48 160 8 3 6 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 48 160 (accept_3_3 23 48 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48
  160 2 11 24 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  48 160 (Polychromatic418967fa.accept_13_8_9_4_1_1552 21 48 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 48 160 4 5 12 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 48 160 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 48 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 160 2 9 24 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 160 (accept_3_3 17 48 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48 160 16 1 3 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 48 160 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 48 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 48 160 2 7 24 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 160
  (Polychromatic418967fa.accept_9_4_3_7_1_296 13 48 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 48 160 4 3 12 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 48 160 (accept_3_3 11 48 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48
  160 2 5 24 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  48 160 (Polychromatic418967fa.accept_15_9_3_10_1_2312 9 48 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 48 160 8 1 6 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 48 160 (Polychromatic418967fa.accept_13_7_9_4_1_918 7 48 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 160 2 3 24 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 160 (accept_3_3 5 48 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 160 4 1 12 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 48 160 (Polychromatic418967fa.accept_21_3_6_13_1_8756 3 48 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 48 160 2 1 24 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 160
  (Polychromatic418967fa.accept_9_1_3_7_1_6 1 48 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 48 160)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 160 (allA_of_3_1 47 47 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 46 160 (allA_succ_of_accept 45 46 160
  (Polychromatic418967fa.accept_7_3_4_6_1_329 45 46 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 46 160 2 22 23 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 46 160 (Polychromatic418967fa.accept_12_7_10_4_1_382 43 46 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 46 160 2 21 23 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 46 160 (accept_3_3 41 46 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 46 160 2 20 23 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 46 160 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 46 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 46 160 2 19 23 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 46 160
  (Polychromatic418967fa.accept_7_2_4_6_1_166 37 46 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 46 160 2 18 23 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 46 160 (accept_3_3 35 46 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 46
  160 2 17 23 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  46 160 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 46 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 46 160 2 16 23 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 46 160 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 46 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 46 160 2 15 23 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 46 160 (accept_3_3 29 46 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 46 160 2 14 23 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 46 160
  (Polychromatic418967fa.accept_21_6_4_13_1_8740 27 46 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 46 160 2 13 23 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 46 160 (Polychromatic418967fa.accept_12_1_10_4_1_380 25 46 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 46 160 2 12 23 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 46 160 (accept_3_3 23 46 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 46 160 2 11 23 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 46 160 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 46 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 46 160 2 10 23 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 46 160
  (Polychromatic418967fa.accept_7_5_4_6_1_167 19 46 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 46 160 2 9 23 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 46 160 (accept_3_3 17 46 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 46
  160 2 8 23 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  46 160 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 46 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 46 160 2 7 23 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 46 160 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 46 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 46 160 2 6 23 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 46 160 (accept_3_3 11 46 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 46 160 2 5 23 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 46 160 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 46 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 46 160 2 4 23 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 46 160
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 46 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 46 160 2 3 23 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 46 160 (accept_3_3 5 46 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 46 160
  2 2 23 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 46
  160 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 46 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 46 160 2 1 23 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 46 160 (Polychromatic418967fa.accept_12_1_10_4_1_380 1 46 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 46 160)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 160
  (allA_succ_of_accept 44 45 160 (accept_3_3 44 45 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  45 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 45 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 45 160 (Polychromatic418967fa.accept_12_6_9_4_1_96 42 45 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 160 (accept_3_3 41 45 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 45 160 5 8 9 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 45 160 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 45 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 160 (accept_3_3 38 45 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 45 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 160
  (Polychromatic418967fa.accept_13_10_6_4_1_1583 36 45 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 45 160 5 7 9 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 45 160 (Polychromatic418967fa.accept_19_15_7_8_1_8755 34 45 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 160 (Polychromatic418967fa.accept_13_7_6_4_1_933 33 45 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 160 (accept_3_3 32 45 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 31
  45 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 45 160 5 6 9 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 45 160 (accept_3_3 29
  45 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 160
  (Polychromatic418967fa.accept_13_2_6_4_1_1593 28 45 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 45 160 (Polychromatic418967fa.accept_11_5_1_6_1_774 27 45 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 160 (accept_3_3 26 45 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 45 160 5 5 9 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 24 45 160 (Polychromatic418967fa.accept_13_11_6_4_1_3121 24 45 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 45 160 (accept_3_3 23 45 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 160 (Polychromatic418967fa.accept_13_9_6_4_1_2243 22 45 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 160
  (Polychromatic418967fa.accept_22_21_1_6_1_8754 21 45 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 45 160 5 4 9 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 45 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 45 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 45 160 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 45 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 160 (accept_3_3 17 45 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 160 (Polychromatic418967fa.accept_7_2_3_6_1_4 16
  45 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 160 5 3 9 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 160 (accept_3_3 14
  45 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 160
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 45 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 45 160 (Polychromatic418967fa.accept_18_12_9_16_1_4732 12 45 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 45 160 (accept_3_3 11 45 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 45 160 5 2 9 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 45 160 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 45 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 160 (accept_3_3 8 45 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 45 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 160
  (Polychromatic418967fa.accept_12_6_9_4_1_96 6 45 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 45 160 5 1 9 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 45 160 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 45 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 45 160 (Polychromatic418967fa.accept_22_3_1_6_1_8753 3 45 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 160 (accept_3_3 2 45 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 45
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  160))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 160 (allA_of_3_1 44 44 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 43 160 (allA_succ_of_accept 42 43 160 (Polychromatic418967fa.accept_15_12_13_10_1_812 42 43 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 43 160 (accept_3_3 41 43 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 43 160 (Polychromatic418967fa.accept_7_5_1_6_1_163 40
  43 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 43 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 43 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 43 160 (accept_3_3 38 43 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  43 160 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 43 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 43 160 (Polychromatic418967fa.accept_17_2_9_7_1_5002 36 43 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 43 160 (accept_3_3 35 43 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 43 160 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 43 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 43 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 43 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 43 160 (accept_3_3 32 43 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  43 160 (Polychromatic418967fa.accept_15_1_13_10_1_1507 31 43 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 43 160 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 43 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 43 160 (accept_3_3 29 43 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 43 160 (Polychromatic418967fa.accept_25_3_18_10_1_8752 28 43 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 43 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 43 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 43 160 (accept_3_3 26 43 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  43 160 (Polychromatic418967fa.accept_21_4_1_13_1_8751 25 43 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 43 160 (Polychromatic418967fa.accept_25_24_18_10_1_8750 24 43 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 43 160 (accept_3_3 23 43 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 43 160 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 43 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 43 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 43 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 43 160 (accept_3_3 20 43 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  43 160 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 43 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 43 160 (Polychromatic418967fa.accept_15_3_13_10_1_2332 18 43 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 43 160 (accept_3_3 17 43 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 43 160 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 43 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 43 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 43 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 43 160 (accept_3_3 14 43 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  43 160 (Polychromatic418967fa.accept_19_13_5_8_1_4487 13 43 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 43 160 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 43 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 43 160 (accept_3_3 11 43 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 43 160 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 43 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 43 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 43 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 43 160 (accept_3_3 8 43 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 43
  160 (Polychromatic418967fa.accept_14_7_1_6_1_3514 7 43 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 43 160 (Polychromatic418967fa.accept_25_6_18_10_1_8749 6 43 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 43 160 (accept_3_3 5 43 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 43 160 (Polychromatic418967fa.accept_15_4_13_10_1_1508 4 43 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 43 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 43 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 43 160 (accept_3_3 2 43 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 43
  160 (Polychromatic418967fa.accept_15_1_13_10_1_1507 1 43 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 43 160))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 160 (allA_succ_of_accept 41 42
  160 (accept_3_3 41 42 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 42 160 2 20 21 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 42 160
  (Polychromatic418967fa.accept_9_3_6_7_1_562 39 42 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 42 160 2 19 21 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 42 160 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 42 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 160 2 18 21 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 160 (accept_3_3 35 42 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 42 160 2 17 21 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 42 160 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 42 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 42 160 2 16 21 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 42 160
  (Polychromatic418967fa.accept_9_4_6_7_1_286 31 42 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 42 160 2 15 21 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 42 160 (accept_3_3 29 42 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42
  160 2 14 21 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  42 160 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 42 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 42 160 2 13 21 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 42 160 (Polychromatic418967fa.accept_11_3_9_6_1_105 25 42 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 160 2 12 21 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 160 (accept_3_3 23 42 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 160 2 11 21 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 42 160
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 42 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 42 160 2 10 21 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 42 160 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 42 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 160 2 9 21 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 160 (accept_3_3 17 42 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 42 160 2 8 21 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 42 160 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 42 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 42 160 2 7 21 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 160 (Polychromatic418967fa.accept_9_4_6_7_1_286 13
  42 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 160 2 6 21 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 160 (accept_3_3 11
  42 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 160 2 5 21 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 42 160
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 42 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 42 160 2 4 21 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 42 160 (Polychromatic418967fa.accept_13_7_3_4_1_459 7 42 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 160 2 3 21 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 160 (accept_3_3 5 42 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 42 160 2 2 21 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 42 160 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 42 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 42 160 2 1 21 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 160 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 42
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42
  160)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 160 (allA_of_3_1 41 41 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 40 160 (allA_succ_of_accept 39 40 160 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 40 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 40 160 2 19 20 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 40 160
  (Polychromatic418967fa.accept_9_1_4_7_1_7 37 40 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 40 160 4 9 10 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 40 160 5 7 8 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 34 40 160 2 17 20 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 40 160 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 40 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 40 160 8 4 5 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 40 160 (Polychromatic418967fa.accept_13_5_1_4_1_3966 31 40 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 40 160 10 3 4 16 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 40 160 (accept_3_3 29 40 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 40 160 4 7 10 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 40 160 (Polychromatic418967fa.accept_14_13_12_6_1_2735
  27 40 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 40 160 2 13 20 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 40 160 5 5 8 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 40 160 8 3 5 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 40 160 (accept_3_3 23
  40 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 40 160 2 11 20 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 40 160
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 40 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 40 160 20 1 2 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 40 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 40 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 40 160 2 9 20 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 40 160 (accept_3_3 17 40 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 40 160 8 2 5 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 40 160 5 3 8 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 40 160 2 7 20 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 40 160 (Polychromatic418967fa.accept_14_13_12_6_1_2735 13 40 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 40 160 4 3 10 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 40 160 (accept_3_3 11 40 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40 160 10 1 4 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 40 160 (Polychromatic418967fa.accept_25_9_15_10_1_8748 9 40 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 40 160 8 1 5 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 40 160
  (Polychromatic418967fa.accept_18_7_4_16_1_2299 7 40 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 40 160 2 3 20 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 40 160 5 1 8 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 40 160 4 1 10 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 40 160 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 40 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 40 160 2 1 20 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 40 160 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 40 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40 160))))))))))))))))))))))))))))))))))))))))
  (allB_succ 39 160 (allA_succ_of_accept 38 39 160 (accept_3_3 38 39 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 39 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 39 160 (Polychromatic418967fa.accept_21_15_18_13_1_8747 36 39
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 39 160 (accept_3_3 35 39 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 160 (Polychromatic418967fa.accept_15_4_9_10_1_5384
  34 39 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 160
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 39 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 39 160 (accept_3_3 32 39 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  39 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 39 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 39 160 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 39 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 39 160 (accept_3_3 29 39 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 160 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 39 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 160
  (Polychromatic418967fa.accept_15_12_9_10_1_2326 27 39 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 39 160 (accept_3_3 26 39 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  39 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 39 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 39 160 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 39 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 39 160 (accept_3_3 23 39 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 160 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 39 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 160
  (Polychromatic418967fa.accept_19_2_1_8_1_7279 21 39 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 39 160 (accept_3_3 20 39 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  39 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 39 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 39 160 (Polychromatic418967fa.accept_12_6_3_4_1_394 18 39 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 39 160 (accept_3_3 17 39 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 160 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 39 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 160
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 39 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 39 160 (accept_3_3 14 39 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  39 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 39 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 39 160 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 39 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 39 160 (accept_3_3 11 39 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 160 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 39 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 160
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 39 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 39 160 (accept_3_3 8 39 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39
  160 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 39 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 39 160 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 39 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 39 160 (accept_3_3 5 39 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 39 160 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 39 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 39 160 (Polychromatic418967fa.accept_7_3_4_6_1_329 3
  39 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 160 (accept_3_3 2 39 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 39
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39
  160))))))))))))))))))))))))))))))))))))))) (allB_succ 38 160 (allA_of_3_1 38 38 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 37 160 (allA_succ_of_accept 36 37 160 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 37 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 160 (accept_3_3 35 37 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 37 160 (Polychromatic418967fa.accept_12_10_1_4_1_392
  34 37 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 37 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 37 160 (accept_3_3 32 37 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  37 160 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 37 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 37 160 (Polychromatic418967fa.accept_9_3_1_7_1_97 30 37 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 160 (accept_3_3 29 37 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 37 160 (Polychromatic418967fa.accept_13_2_11_4_1_445 28 37 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 37 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 37 160 (accept_3_3 26 37 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  37 160 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 37 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 37 160 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 37 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 160 (accept_3_3 23 37 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 37 160 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 37 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 37 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 37 160 (accept_3_3 20 37 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  37 160 (Polychromatic418967fa.accept_13_6_11_4_1_938 19 37 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 37 160 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 37 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 160 (accept_3_3 17 37 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 37 160 (Polychromatic418967fa.accept_15_1_7_10_1_287 16 37 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 37 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 37 160 (accept_3_3 14 37 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  37 160 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 37 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 37 160 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 37 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 37 160 (accept_3_3 11 37 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 37 160 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 37 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 37 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 37 160 (accept_3_3 8 37 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37
  160 (Polychromatic418967fa.accept_13_7_11_4_1_2247 7 37 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 37 160 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 37 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 37 160 (accept_3_3 5 37 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 37 160 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 37 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 37 160
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 37 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 37 160 (accept_3_3 2 37 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 37
  160 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 37 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 37 160))))))))))))))))))))))))))))))))))))) (allB_succ 36 160 (allA_succ_of_accept 35 36 160 (accept_3_3 35
  36 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 36 160 2 17 18 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 36 160
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 36 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 36 160 4 8 9 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 36 160 (Polychromatic418967fa.accept_11_9_3_6_1_797 31 36 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 160 2 15 18 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 160 (accept_3_3 29 36 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 160 4 7 9 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 36 160 (Polychromatic418967fa.accept_13_1_10_4_1_954 27 36 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 36 160 2 13 18 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 36 160
  (Polychromatic418967fa.accept_19_6_17_8_1_8746 25 36 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 36 160 4 6 9 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 36 160 (accept_3_3 23 36 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36
  160 2 11 18 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  36 160 (Polychromatic418967fa.accept_13_8_10_4_1_2270 21 36 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 36 160 4 5 9 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 36 160 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 36 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 160 2 9 18 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 160 (accept_3_3 17 36 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 160 4 4 9 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 36 160 (Polychromatic418967fa.accept_17_15_2_7_1_7389 15 36 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 36 160 2 7 18 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 36 160
  (Polychromatic418967fa.accept_17_13_2_7_1_6122 13 36 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 36 160 4 3 9 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 36 160 (accept_3_3 11 36 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 36
  160 2 5 18 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  36 160 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 36 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 36 160 4 2 9 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 36 160 (Polychromatic418967fa.accept_13_7_10_4_1_919 7 36 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 160 2 3 18 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 160 (accept_3_3 5 36 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 160 4 1 9 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 36 160 (Polychromatic418967fa.accept_15_3_6_10_1_1539 3 36 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 36 160 2 1 18 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 36 160
  (Polychromatic418967fa.accept_13_1_10_4_1_954 1 36 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 36 160)))))))))))))))))))))))))))))))))))) (allB_succ 35 160 (allA_of_3_1 35 35 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 34 160 (allA_succ_of_accept 33 34 160 (Polychromatic418967fa.accept_23_10_11_22_1_8745
  33 34 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 34 160 2 16 17 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 34 160
  (Polychromatic418967fa.accept_12_7_10_4_1_382 31 34 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 34 160 2 15 17 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 34 160 (accept_3_3 29 34 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 34
  160 2 14 17 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  34 160 (Polychromatic418967fa.accept_11_5_1_6_1_774 27 34 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 34 160 2 13 17 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 34 160 (Polychromatic418967fa.accept_12_1_10_4_1_380 25 34 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 34 160 2 12 17 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 34 160 (accept_3_3 23 34 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 34 160 2 11 17 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 34 160
  (Polychromatic418967fa.accept_15_6_4_10_1_2319 21 34 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 34 160 2 10 17 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 34 160 (Polychromatic418967fa.accept_12_7_10_4_1_382 19 34 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 34 160 2 9 17 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 34 160 (accept_3_3 17 34 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 34 160 2 8 17 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 34 160 (Polychromatic418967fa.accept_22_15_12_6_1_8744 15 34 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 34 160 2 7 17 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 34 160
  (Polychromatic418967fa.accept_12_1_10_4_1_380 13 34 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 34 160 2 6 17 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 34 160 (accept_3_3 11 34 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 34
  160 2 5 17 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  34 160 (Polychromatic418967fa.accept_13_9_8_4_1_937 9 34 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 34 160 2 4 17 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 34 160 (Polychromatic418967fa.accept_11_7_1_6_1_1281 7 34 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 34 160 2 3 17 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 34 160 (accept_3_3 5 34 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 34 160 2 2 17 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 34 160 (Polychromatic418967fa.accept_19_3_15_8_1_3232 3 34 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 34 160 2 1 17 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 34 160
  (Polychromatic418967fa.accept_12_1_10_4_1_380 1 34 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 34 160)))))))))))))))))))))))))))))))))) (allB_succ 33 160 (allA_succ_of_accept 32 33 160 (accept_3_3 32 33
  160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 160 (Polychromatic418967fa.accept_6_1_3_4_1_1
  31 33 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 160
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 33 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 33 160 (accept_3_3 29 33 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  33 160 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 33 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 33 160 (Polychromatic418967fa.accept_14_13_5_6_1_2747 27 33 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 160 (accept_3_3 26 33 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 33 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 33 160
  (Polychromatic418967fa.accept_13_11_7_4_1_1561 24 33 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 33 160 (accept_3_3 23 33 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  33 160 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 33 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 33 160 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 33 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 160 (accept_3_3 20 33 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 33 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 160
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 33 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 33 160 (accept_3_3 17 33 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  33 160 (Polychromatic418967fa.accept_13_3_7_4_1_435 16 33 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 33 160 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 33 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 160 (accept_3_3 14 33 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 33 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 160
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 33 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 33 160 (accept_3_3 11 33 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  33 160 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 33 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 33 160 (Polychromatic418967fa.accept_13_9_7_4_1_953 9 33 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 160 (accept_3_3 8 33 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 33 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 160
  (Polychromatic418967fa.accept_12_6_9_4_1_96 6 33 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 160 (accept_3_3 5 33 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33
  160 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 33 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 33 160 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 33 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 160 (accept_3_3 2 33 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 33 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 33 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 160))))))))))))))))))))))))))))))))) (allB_succ 32 160
  (allA_of_3_1 32 32 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 31 160 (allA_succ_of_accept 30 31 160
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 31 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 31 160 (accept_3_3 29 31 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  31 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 31 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 31 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 31 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 160 (accept_3_3 26 31 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 160 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 31 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 160
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 31 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 160 (accept_3_3 23 31 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  31 160 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 31 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 31 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 31 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 160 (accept_3_3 20 31 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 31 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 160
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 31 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 160 (accept_3_3 17 31 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 160 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 31 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 31 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 160 (accept_3_3 14 31 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 160 (Polychromatic418967fa.accept_15_13_1_10_1_816 13 31 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 160
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 31 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 160 (accept_3_3 11 31 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 31 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 31 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 160 (accept_3_3 8 31 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 160 (Polychromatic418967fa.accept_15_7_1_10_1_305 7 31 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 160
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 31 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 160 (accept_3_3 5 31 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  160 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 31 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 31 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 31 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 160 (accept_3_3 2 31 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 31 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 31 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 160))))))))))))))))))))))))))))))) (allB_succ 30 160
  (allA_succ_of_accept 29 30 160 (accept_3_3 29 30 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30
  160 2 14 15 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  30 160 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 30 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 30 160 2 13 15 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 25 30 160 5 5 6 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 30 160 2 12 15 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 30 160 (accept_3_3 23 30 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 30 160 2 11 15 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 30 160 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 30 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 30 160 10 2 3 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 30 160 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 30 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 160 2 9 15 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 160 (accept_3_3 17 30 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 160 2 8 15 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 30 160 5 3 6 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 30 160 2 7 15 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 160 (Polychromatic418967fa.accept_9_4_3_7_1_296 13
  30 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 160 2 6 15 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 160 (accept_3_3 11
  30 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 160 10 1 3 16 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 30 160
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 30 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 30 160 2 4 15 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 30 160 (Polychromatic418967fa.accept_19_7_11_8_1_8743 7 30 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 160 2 3 15 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 30 160 5 1 6 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 30 160 2 2 15 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 30 160 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 30 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 30 160 2 1 15 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 160
  (Polychromatic418967fa.accept_7_1_2_6_1_55 1 30 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 30 160)))))))))))))))))))))))))))))) (allB_succ 29 160 (allA_of_3_1 29 29 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 28 160 (allA_succ_of_accept 27 28 160 (Polychromatic418967fa.accept_15_12_13_10_1_812 27 28 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 28 160 2 13 14 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 28 160
  (Polychromatic418967fa.accept_13_12_2_4_1_3131 25 28 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 28 160 4 6 7 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 28 160 (accept_3_3 23 28 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 28
  160 2 11 14 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  28 160 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 28 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 28 160 4 5 7 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 28 160 (Polychromatic418967fa.accept_13_6_2_4_1_923 19 28 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 28 160 2 9 14 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 28 160 (accept_3_3 17 28 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 28 160 4 4 7 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 28 160 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 28 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 28 160 2 7 14 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 28 160
  (Polychromatic418967fa.accept_9_4_1_7_1_293 13 28 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 28 160 4 3 7 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 28 160 (accept_3_3 11 28 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 28
  160 2 5 14 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  28 160 (Polychromatic418967fa.accept_21_9_7_13_1_8742 9 28 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 28 160 4 2 7 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 28 160 (Polychromatic418967fa.accept_19_7_9_8_1_7297 7 28 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 28 160 2 3 14 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 28 160 (accept_3_3 5 28 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 28 160 4 1 7 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 28 160 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 28 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 28 160 2 1 14 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 28 160
  (Polychromatic418967fa.accept_15_1_13_10_1_1507 1 28 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 28 160)))))))))))))))))))))))))))) (allB_succ 27 160 (allA_succ_of_accept 26 27 160 (accept_3_3 26 27 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 25
  27 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 160
  (Polychromatic418967fa.accept_15_9_12_10_1_809 24 27 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 27 160 (accept_3_3 23 27 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  27 160 (Polychromatic418967fa.accept_15_7_12_10_1_4335 22 27 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 27 160 (Polychromatic418967fa.accept_11_10_5_6_1_1842 21 27 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 160 (accept_3_3 20 27 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 27 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 27 160
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 27 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 27 160 (accept_3_3 17 27 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  27 160 (Polychromatic418967fa.accept_13_3_1_4_1_945 16 27 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 27 160 (Polychromatic418967fa.accept_18_15_9_16_1_6029 15 27 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 160 (accept_3_3 14 27 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 27 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 27 160
  (Polychromatic418967fa.accept_11_1_5_6_1_397 12 27 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 27 160 (accept_3_3 11 27 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  27 160 (Polychromatic418967fa.accept_11_10_5_6_1_1842 10 27 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 27 160 (Polychromatic418967fa.accept_15_9_12_10_1_809 9 27 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 160 (accept_3_3 8 27 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 27 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27 160
  (Polychromatic418967fa.accept_12_6_3_4_1_394 6 27 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 27 160 (accept_3_3 5 27 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27
  160 (Polychromatic418967fa.accept_21_4_6_13_1_7137 4 27 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 27 160 (Polychromatic418967fa.accept_13_3_1_4_1_945 3 27 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 160 (accept_3_3 2 27 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 27 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 160))))))))))))))))))))))))))) (allB_succ 26 160
  (allA_of_3_1 26 26 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 25 160 (allA_succ_of_accept 24 25 160
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 25 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 160 (accept_3_3 23 25 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  25 160 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 25 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 25 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 25 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 25 160 5 4 5 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 25 160 (Polychromatic418967fa.accept_7_5_4_6_1_167 19
  25 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 160
  (Polychromatic418967fa.accept_13_5_12_4_1_449 18 25 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 160 (accept_3_3 17 25 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 160 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 25 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 25 160 5 3 5 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 25 160 (accept_3_3 14 25 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 25 160 (Polychromatic418967fa.accept_19_13_6_8_1_8741 13 25 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 160 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 25 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 160 (accept_3_3 11 25 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 25 160 5 2 5 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 25 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 25
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 160 (accept_3_3 8 25 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 160 (Polychromatic418967fa.accept_13_7_12_4_1_450 7
  25 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 160
  (Polychromatic418967fa.accept_21_6_4_13_1_8740 6 25 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 25 160 5 1 5 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 25 160 (Polychromatic418967fa.accept_17_4_8_7_1_7469 4 25 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 25 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 160 (accept_3_3 2 25 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25 160 (Polychromatic418967fa.accept_17_1_8_7_1_4982 1
  25 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 160)))))))))))))))))))))))))
  (allB_succ 24 160 (allA_succ_of_accept 23 24 160 (accept_3_3 23 24 160 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 24 160 2 11 12 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 24 160 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 24 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 24 160 4 5 6 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 24 160 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 24 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 160 2 9 12 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 160 (accept_3_3 17 24 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 24 160 8 2 3 20 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 24 160 (Polychromatic418967fa.accept_11_4_2_6_1_389 15
  24 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 24 160 2 7 12 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 160
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 24 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 24 160 4 3 6 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 24 160 (accept_3_3 11 24 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24
  160 2 5 12 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  24 160 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 24 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 24 160 8 1 3 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 24 160 (Polychromatic418967fa.accept_13_7_11_4_1_2247 7 24 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 160 2 3 12 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24 160 (accept_3_3 5 24 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 24 160 4 1 6 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 24 160 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 24 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 24 160 2 1 12 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 160 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 24
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 160)))))))))))))))))))))))) (allB_succ
  23 160 (allA_of_3_1 23 23 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 22 160 (allA_succ_of_accept 21 22
  160 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 22 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 22 160 2 10 11 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 22 160 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 22 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 22 160 2 9 11 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 22 160 (accept_3_3 17 22 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 22 160 2 8 11 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 22 160 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 22 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 22 160 2 7 11 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 22 160 (Polychromatic418967fa.accept_12_1_10_4_1_380
  13 22 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 22 160 2 6 11 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 22 160 (accept_3_3 11
  22 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 22 160 2 5 11 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 22 160
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 22 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 22 160 2 4 11 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 22 160 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 22 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 22 160 2 3 11 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 22 160 (accept_3_3 5 22 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 22 160 2 2 11 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 22 160 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 22 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 22 160 2 1 11 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 22 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 22
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 160)))))))))))))))))))))) (allB_succ 21
  160 (allA_succ_of_accept 20 21 160 (accept_3_3 20 21 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 21 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 21 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 21 160 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 21 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 160 (accept_3_3 17 21 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 160 (Polychromatic418967fa.accept_11_5_10_6_1_793 16 21 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 160
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 21 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 21 160 (accept_3_3 14 21 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  21 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 21 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 21 160 (Polychromatic418967fa.accept_13_12_8_4_1_3099 12 21 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 160 (accept_3_3 11 21 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 160 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 21 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 160
  (Polychromatic418967fa.accept_13_9_8_4_1_937 9 21 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 21 160 (accept_3_3 8 21 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21
  160 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 21 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 21 160 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 21 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 160 (accept_3_3 5 21 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 21 160 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 21 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21 160 (Polychromatic418967fa.accept_15_3_6_10_1_1539
  3 21 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 160 (accept_3_3 2 21
  160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  21 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 160))))))))))))))))))))) (allB_succ
  20 160 (allA_of_3_1 20 20 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 19 160 (allA_succ_of_accept 18 19
  160 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 19 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 160 (accept_3_3 17 19 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 160 (Polychromatic418967fa.accept_21_16_19_13_1_7140 16 19 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 19 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 160 (accept_3_3 14 19 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 160 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 19 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 160
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 19 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 160 (accept_3_3 11 19 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 160 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 19 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 19 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 160 (accept_3_3 8 19 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 160 (Polychromatic418967fa.accept_13_7_6_4_1_933 7 19 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 160
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 19 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 160 (accept_3_3 5 19 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  160 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 19 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 19 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 160 (accept_3_3 2 19 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 160 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 19 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 160))))))))))))))))))) (allB_succ 18 160 (allA_succ_of_accept 17
  18 160 (accept_3_3 17 18 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 160 2 8 9 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 18 160
  (Polychromatic418967fa.accept_12_3_6_4_1_400 15 18 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 18 160 2 7 9 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 18 160 (Polychromatic418967fa.accept_15_13_3_10_1_2296 13 18 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 160 2 6 9 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 160 (accept_3_3 11 18 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 18 160 2 5 9 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 18 160 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 18 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 160 2 4 9 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 160 (Polychromatic418967fa.accept_15_7_3_10_1_817 7
  18 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 160 2 3 9 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 160 (accept_3_3 5 18
  160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 160 2 2 9 80 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18 160
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 18 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 18 160 2 1 9 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 18 160 (Polychromatic418967fa.accept_11_1_7_6_1_378 1 18 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 18 160)))))))))))))))))) (allB_succ 17 160 (allA_of_3_1 17 17 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 16 160 (allA_succ_of_accept 15 16 160
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 16 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 16 160 2 7 8 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 16 160 (Polychromatic418967fa.accept_15_13_1_10_1_816 13 16 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 16 160 4 3 4 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 16 160 (accept_3_3 11 16 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 16 160 2 5 8 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 16 160 (Polychromatic418967fa.accept_15_9_1_10_1_4316 9 16 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 16 160 8 1 2 20 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 16 160 (Polychromatic418967fa.accept_13_7_3_4_1_459 7
  16 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 16 160 2 3 8 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 16 160 (accept_3_3 5 16
  160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 16 160 4 1 4 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 16 160
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 16 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 16 160 2 1 8 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 16 160 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 16 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 16 160)))))))))))))))) (allB_succ 15 160 (allA_succ_of_accept 14 15 160
  (accept_3_3 14 15 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 160
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 15 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 15 160 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 15 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 160 (accept_3_3 11 15 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 15 160 5 2 3 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 15 160 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 15 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 160 (accept_3_3 8 15 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 15 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 160
  (Polychromatic418967fa.accept_12_6_3_4_1_394 6 15 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 15 160 5 1 3 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 15 160 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 15 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 15 160 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 15 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 160 (accept_3_3 2 15 160
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 15
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 160))))))))))))))) (allB_succ 14 160
  (allA_of_3_1 14 14 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 160 (allA_succ_of_accept 12 13 160
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 13 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 160 (accept_3_3 11 13 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 13 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 13 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 160 (accept_3_3 8 13 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 160 (Polychromatic418967fa.accept_14_7_13_6_1_1177 7 13 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 160
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 13 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 160 (accept_3_3 5 13 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  160 (Polychromatic418967fa.accept_11_4_2_6_1_389 4 13 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 13 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 160 (accept_3_3 2 13 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 160 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 13 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 160))))))))))))) (allB_succ 12 160 (allA_succ_of_accept 11 12
  160 (accept_3_3 11 12 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 12 160 2 5 6 80 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 12 160
  (Polychromatic418967fa.accept_15_9_12_10_1_809 9 12 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 12 160 4 2 3 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 12 160 (Polychromatic418967fa.accept_11_7_1_6_1_1281 7 12 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 160 2 3 6 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 160 (accept_3_3 5 12 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 12 160 4 1 3 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 12 160 (Polychromatic418967fa.accept_13_3_12_4_1_110 3 12 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 160 2 1 6 80 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 160 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 12
  160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 160)))))))))))) (allB_succ 11 160
  (allA_of_3_1 11 11 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 10 160 (allA_succ_of_accept 9 10 160
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 10 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 10 160 2 4 5 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 10 160 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 10 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 10 160 2 3 5 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 10 160 5 1 2 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 10 160 2 2 5 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 10 160 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 10 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 10 160 2 1 5 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 10 160
  (Polychromatic418967fa.accept_12_1_10_4_1_380 1 10 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 10 160)))))))))) (allB_succ 9 160 (allA_succ_of_accept 8 9 160 (accept_3_3 8 9 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 9 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 160
  (Polychromatic418967fa.accept_12_6_9_4_1_96 6 9 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 9 160 (accept_3_3 5 9 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 160
  (Polychromatic418967fa.accept_7_4_2_6_1_337 4 9 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 9 160 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 9 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 160 (accept_3_3 2 9 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 9 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 9 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 160))))))))) (allB_succ 8 160 (allA_of_3_1 8 8 160 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 7 160 (allA_succ_of_accept 6 7 160
  (Polychromatic418967fa.accept_13_6_7_4_1_2264 6 7 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 160 (accept_3_3 5 7 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 160
  (Polychromatic418967fa.accept_15_4_7_10_1_807 4 7 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 160 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 7 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 160 (accept_3_3 2 7 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 160 (Polychromatic418967fa.accept_11_1_7_6_1_378 1 7 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 160))))))) (allB_succ 6 160 (allA_succ_of_accept 5 6 160
  (accept_3_3 5 6 160 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 160 2 2 3 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 160
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 6 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 6 160 2 1 3 80 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 160 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 6 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 6 160)))))) (allB_succ 5 160 (allA_of_3_1 5 5 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 4 160 (allA_succ_of_accept 3 4 160 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 4 160
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 4 160 2 1 2 80 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 4 160
  (Polychromatic418967fa.accept_9_1_4_7_1_7 1 4 160 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 160)))) (allB_succ 3 160 (allA_succ_of_accept 2 3 160 (accept_3_3 2 3 160 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 160 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 3 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 160))) (allB_succ 2 160 (allA_of_3_1 2 2 160 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  160))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


