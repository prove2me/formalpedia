-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch166
-- name    : Polychromatic418967fa_Branch166
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:18:53.695275+00:00
-- url     : https://prove2.me/theorems/37196bc2-b137-4a24-9dc0-d5e1aefe35c0
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

def Polychromatic418967fa.branch_166 : allB 166 166 :=
  allB_succ' 2 165 166 (Eq.refl Bool.true) (allA_succ_of_accept 1 165 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  165 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 165 166)) (allB_succ' 3 164 166
  (Eq.refl Bool.true) (allA_of_3_1 3 164 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 163 166 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 163 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 163 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 163 166 (accept_3_3 2 163 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 163 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 163 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 163 166)))) (allB_succ' 5 162 166 (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 162 166 2 2 81 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 162 166 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 162 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 162 166 2 1 81 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 162 166 (Polychromatic418967fa.accept_10_1_2_6_1_638 1 162 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162 166))))) (allB_succ' 6 161 166 (Eq.refl
  Bool.true) (allA_of_3_1 6 161 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 160 166 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 160 166 2 3 80 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 160 166 (accept_3_3 5 160 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 160
  166 2 2 80 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  160 166 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 160 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 160 166 2 1 80 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 160 166 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 160 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 160 166))))))) (allB_succ' 8 159 166 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 159 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 159 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 159 166 (Polychromatic418967fa.accept_11_6_5_1_1_586 6 159 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 159 166 (accept_3_3 5 159 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 159 166 (Polychromatic418967fa.accept_19_4_7_14_1_3537
  4 159 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 159 166
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 159 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 159 166 (accept_3_3 2 159 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  159 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 159 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 159 166)))))))) (allB_succ' 9 158 166 (Eq.refl Bool.true) (allA_of_3_1 9 158 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 157 166 (Eq.refl Bool.true) (allA_succ_of_accept 9 157 166
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 157 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 157 166 (accept_3_3 8 157 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  157 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 157 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 157 166 (Polychromatic418967fa.accept_15_6_7_1_1_93 6 157 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 157 166 (accept_3_3 5 157 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 157 166 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 157 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 157 166
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 157 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 157 166 (accept_3_3 2 157 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  157 166 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 157 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 157 166)))))))))) (allB_succ' 11 156 166 (Eq.refl Bool.true) (allA_succ_of_gcd 10 156 166 2 5 78
  83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 156 166
  (Polychromatic418967fa.accept_15_9_6_1_1_493 9 156 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 156 166 2 4 78 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 156 166 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 156 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 156 166 2 3 78 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 156 166 (accept_3_3 5 156 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 156 166 2 2 78 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 156 166 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 156 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 156 166 2 1 78 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 156 166 (Polychromatic418967fa.accept_9_1_3_4_1_47 1
  156 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156 166))))))))))) (allB_succ' 12 155
  166 (Eq.refl Bool.true) (allA_of_3_1 12 155 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 154 166
  (Eq.refl Bool.true) (allA_succ_of_gcd 12 154 166 2 6 77 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 154 166 (accept_3_3 11 154 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 154 166 2 5 77 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 154 166 (Polychromatic418967fa.accept_20_9_14_6_1_320 9 154 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 154 166 2 4 77 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 154 166 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 154 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 154 166 2 3 77 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 154 166 (accept_3_3 5 154 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 154 166 2 2 77 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 154 166 (Polychromatic418967fa.accept_9_3_1_4_1_216 3
  154 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 154 166 2 1 77 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 154 166
  (Polychromatic418967fa.accept_13_1_11_10_1_1258 1 154 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 154 166))))))))))))) (allB_succ' 14 153 166 (Eq.refl Bool.true) (allA_succ_of_accept 13 153 166
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 153 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 153 166 (Polychromatic418967fa.accept_18_12_9_4_1_2740 12 153 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 153 166 (accept_3_3 11 153 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 153 166 (Polychromatic418967fa.accept_19_10_1_14_1_9224 10 153 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 153 166
  (Polychromatic418967fa.accept_10_9_3_6_1_686 9 153 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 153 166 (accept_3_3 8 153 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  153 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 153 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 153 166 (Polychromatic418967fa.accept_12_6_9_10_1_565 6 153 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 153 166 (accept_3_3 5 153 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 166 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 153 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 153 166
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 153 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 153 166 (accept_3_3 2 153 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  153 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 153 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 153 166)))))))))))))) (allB_succ' 15 152 166 (Eq.refl Bool.true) (allA_of_3_1 15 152 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 151 166 (Eq.refl Bool.true) (allA_succ_of_accept 15 151 166
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 151 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 151 166 (accept_3_3 14 151 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 151 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 151 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 151 166 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 151 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 151 166 (accept_3_3 11 151 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 151 166 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 151 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 151 166
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 151 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 151 166 (accept_3_3 8 151 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  151 166 (Polychromatic418967fa.accept_10_7_1_6_1_673 7 151 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 151 166 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 151 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 151 166 (accept_3_3 5 151 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 151 166 (Polychromatic418967fa.accept_11_4_8_1_1_1047 4 151 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 151 166
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 151 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 151 166 (accept_3_3 2 151 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  151 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 151 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 151 166)))))))))))))))) (allB_succ' 17 150 166 (Eq.refl Bool.true) (allA_succ_of_gcd 16 150 166
  2 8 75 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 150
  166 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 150 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 150 166 2 7 75 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 150 166 (Polychromatic418967fa.accept_24_13_6_22_1_2345 13 150 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 150 166 2 6 75 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 150 166 (accept_3_3 11 150 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 150 166 2 5 75 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 150 166 (Polychromatic418967fa.accept_7_2_3_5_1_34 9
  150 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 150 166 2 4 75 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 150 166
  (Polychromatic418967fa.accept_9_7_6_4_1_483 7 150 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 150 166 2 3 75 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 150 166 (accept_3_3 5 150 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 150
  166 2 2 75 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  150 166 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 150 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 150 166 2 1 75 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 150 166 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 150 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150 166))))))))))))))))) (allB_succ' 18 149 166 (Eq.refl Bool.true)
  (allA_of_3_1 18 149 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 148 166 (Eq.refl Bool.true)
  (allA_succ_of_gcd 18 148 166 2 9 74 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 148 166 (accept_3_3 17 148 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  148 166 2 8 74 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 148 166 (Polychromatic418967fa.accept_13_2_5_10_1_250 15 148 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 148 166 2 7 74 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 148 166 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 148 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 148 166 2 6 74 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 148 166 (accept_3_3 11 148 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 148 166 2 5 74 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 148 166
  (Polychromatic418967fa.accept_27_9_13_4_1_7170 9 148 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 148 166 2 4 74 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 148 166 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 148 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 148 166 2 3 74 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 148 166 (accept_3_3 5 148 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 148 166 2 2 74 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 148 166 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 148 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 148 166 2 1 74 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 148 166 (Polychromatic418967fa.accept_12_1_4_10_1_209 1
  148 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 148 166))))))))))))))))))) (allB_succ'
  20 147 166 (Eq.refl Bool.true) (allA_succ_of_accept 19 147 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 147 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 147 166
  (Polychromatic418967fa.accept_12_6_3_10_1_224 18 147 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 147 166 (accept_3_3 17 147 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 147 166 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 147 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 147 166 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 147 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 147 166 (accept_3_3 14 147 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 147 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 147 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 147 166
  (Polychromatic418967fa.accept_17_12_11_13_1_5378 12 147 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 147 166 (accept_3_3 11 147 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 147 166 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 147 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 147 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 147 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 147 166 (accept_3_3 8 147 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 7
  147 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 147 166
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 147 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 147 166 (accept_3_3 5 147 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  147 166 (Polychromatic418967fa.accept_15_4_12_1_1_1081 4 147 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 147 166 (Polychromatic418967fa.accept_10_3_7_6_1_659 3 147 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 147 166 (accept_3_3 2 147 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 147 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 147 166)))))))))))))))))))) (allB_succ' 21 146 166
  (Eq.refl Bool.true) (allA_of_3_1 21 146 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 145 166 (Eq.refl
  Bool.true) (allA_succ_of_accept 21 145 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 145 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 145 166 (accept_3_3 20 145 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 145 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 145 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 145 166
  (Polychromatic418967fa.accept_13_5_2_10_1_248 18 145 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 145 166 (accept_3_3 17 145 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 145 166 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 145 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 145 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 145 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 145 166 (accept_3_3 14 145 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 145 166 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 145 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 145 166
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 145 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 145 166 (accept_3_3 11 145 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 145 166 (Polychromatic418967fa.accept_11_10_2_1_1_1036 10 145 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 145 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 145 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 145 166 (accept_3_3 8 145 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 145 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 145 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 145 166
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 145 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 145 166 (accept_3_3 5 145 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  145 166 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 145 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 145 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 145 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 145 166 (accept_3_3 2 145 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 145 166 (Polychromatic418967fa.accept_10_1_5_6_1_649 1 145 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 145 166)))))))))))))))))))))) (allB_succ' 23 144 166
  (Eq.refl Bool.true) (allA_succ_of_gcd 22 144 166 2 11 72 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 144 166 (Polychromatic418967fa.accept_15_6_9_1_1_1823 21 144
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 144 166 2 10 72 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 144 166
  (Polychromatic418967fa.accept_27_19_9_4_1_9223 19 144 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 144 166 2 9 72 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 144 166 (accept_3_3 17 144 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  144 166 2 8 72 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 144 166 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 144 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 144 166 2 7 72 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 144 166 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 144 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 144 166 2 6 72 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 144 166 (accept_3_3 11 144 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 144 166 2 5 72 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 144 166
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 144 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 144 166 2 4 72 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 144 166 (Polychromatic418967fa.accept_15_7_9_1_1_473 7 144 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 144 166 2 3 72 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 144 166 (accept_3_3 5 144 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 144 166 2 2 72 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 144 166 (Polychromatic418967fa.accept_17_3_8_13_1_5361 3 144 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 144 166 2 1 72 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 144 166 (Polychromatic418967fa.accept_7_1_4_5_1_35 1
  144 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144 166)))))))))))))))))))))))
  (allB_succ' 24 143 166 (Eq.refl Bool.true) (allA_of_3_1 24 143 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 25 142 166 (Eq.refl Bool.true) (allA_succ_of_gcd 24 142 166 2 12 71 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 142 166 (accept_3_3 23 142 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 142 166 2 11 71 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 142 166 (Polychromatic418967fa.accept_9_3_7_4_1_53 21
  142 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 142 166 2 10 71 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 142 166
  (Polychromatic418967fa.accept_9_1_7_4_1_52 19 142 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 142 166 2 9 71 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 142 166 (accept_3_3 17 142 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  142 166 2 8 71 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 142 166 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 142 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 142 166 2 7 71 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 142 166 (Polychromatic418967fa.accept_11_2_10_1_1_1017 13 142 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 142 166 2 6 71 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 142 166 (accept_3_3 11 142 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 142 166 2 5 71 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 142 166
  (Polychromatic418967fa.accept_11_9_10_1_1_581 9 142 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 142 166 2 4 71 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 142 166 (Polychromatic418967fa.accept_13_7_12_10_1_640 7 142 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 142 166 2 3 71 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 142 166 (accept_3_3 5 142 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 142 166 2 2 71 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 142 166 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 142 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 142 166 2 1 71 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 142 166 (Polychromatic418967fa.accept_9_1_7_4_1_52 1
  142 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142 166)))))))))))))))))))))))))
  (allB_succ' 26 141 166 (Eq.refl Bool.true) (allA_succ_of_accept 25 141 166 (Polychromatic418967fa.accept_6_1_3_4_1_1
  25 141 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 141 166
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 141 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 141 166 (accept_3_3 23 141 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 141 166 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 141 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 141 166 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 141 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 141 166 (accept_3_3 20 141 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 141 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 141 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 141 166
  (Polychromatic418967fa.accept_7_4_1_5_1_540 18 141 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 141 166 (accept_3_3 17 141 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 141 166 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 141 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 141 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 141 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 141 166 (accept_3_3 14 141 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 141 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 141 166
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 141 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 141 166 (accept_3_3 11 141 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 141 166 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 141 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 141 166 (Polychromatic418967fa.accept_15_9_6_1_1_493 9 141 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 141 166 (accept_3_3 8 141 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 141 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 141 166
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 141 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 141 166 (accept_3_3 5 141 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  141 166 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 141 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 141 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 141 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 141 166 (accept_3_3 2 141 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 141 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 141 166)))))))))))))))))))))))))) (allB_succ' 27 140 166
  (Eq.refl Bool.true) (allA_of_3_1 27 140 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 139 166 (Eq.refl
  Bool.true) (allA_succ_of_accept 27 139 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 139 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 139 166 (accept_3_3 26 139 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 139 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 139 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 139 166
  (Polychromatic418967fa.accept_19_5_6_14_1_5010 24 139 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 139 166 (accept_3_3 23 139 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 139 166 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 139 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 139 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 139 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 139 166 (accept_3_3 20 139 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 139 166 (Polychromatic418967fa.accept_13_6_9_10_1_1201 19 139 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 139 166
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 139 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 139 166 (accept_3_3 17 139 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 139 166 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 139 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 139 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 139 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 139 166 (accept_3_3 14 139 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 139 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 139 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 139 166
  (Polychromatic418967fa.accept_13_12_9_10_1_1223 12 139 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 139 166 (accept_3_3 11 139 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 139 166 (Polychromatic418967fa.accept_17_10_3_13_1_6639 10 139 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 139 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 9
  139 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 139 166 (accept_3_3 8 139
  166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 139 166
  (Polychromatic418967fa.accept_18_7_13_4_1_1670 7 139 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 139 166 (Polychromatic418967fa.accept_11_6_7_1_1_564 6 139 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 139 166 (accept_3_3 5 139 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 139 166 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 139 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 139 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 3
  139 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 139 166 (accept_3_3 2 139
  166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 139 166 (Polychromatic418967fa.accept_4_1_3_2_1_3
  1 139 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 139 166))))))))))))))))))))))))))))
  (allB_succ' 29 138 166 (Eq.refl Bool.true) (allA_succ_of_gcd 28 138 166 2 14 69 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 138 166
  (Polychromatic418967fa.accept_11_5_6_1_1_988 27 138 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 138 166 2 13 69 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 138 166 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 138 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 138 166 2 12 69 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 138 166 (accept_3_3 23 138 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 138 166 2 11 69 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 138 166 (Polychromatic418967fa.accept_12_9_6_10_1_1085
  21 138 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 138 166 2 10 69 83
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 138 166
  (Polychromatic418967fa.accept_9_1_3_4_1_47 19 138 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 138 166 2 9 69 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 138 166 (accept_3_3 17 138 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  138 166 2 8 69 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 138 166 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 138 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 138 166 2 7 69 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 138 166 (Polychromatic418967fa.accept_10_3_8_6_1_326 13 138 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 138 166 2 6 69 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 138 166 (accept_3_3 11 138 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 138 166 2 5 69 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 138 166
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 138 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 138 166 2 4 69 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 138 166 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 138 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 138 166 2 3 69 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 138 166 (accept_3_3 5 138 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 138 166 2 2 69 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 138 166 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 138 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 138 166 2 1 69 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 138 166 (Polychromatic418967fa.accept_9_1_3_4_1_47 1
  138 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138 166)))))))))))))))))))))))))))))
  (allB_succ' 30 137 166 (Eq.refl Bool.true) (allA_of_3_1 30 137 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 31 136 166 (Eq.refl Bool.true) (allA_succ_of_gcd 30 136 166 2 15 68 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 136 166 (accept_3_3 29 136 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 136 166 2 14 68 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 136 166 (Polychromatic418967fa.accept_19_8_3_14_1_3571
  27 136 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 136 166 2 13 68 83
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 136 166
  (Polychromatic418967fa.accept_9_7_1_4_1_217 25 136 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 136 166 2 12 68 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 136 166 (accept_3_3 23 136 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 136 166 2 11 68 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 136 166 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 136 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 136 166 2 10 68 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 136 166
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 19 136 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 136 166 2 9 68 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 136 166 (accept_3_3 17 136 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  136 166 2 8 68 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 136 166 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 136 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 136 166 2 7 68 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 136 166 (Polychromatic418967fa.accept_12_1_4_10_1_209 13 136 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 136 166 2 6 68 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 136 166 (accept_3_3 11 136 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 136 166 2 5 68 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 136 166
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 136 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 136 166 2 4 68 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 136 166 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 136 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 136 166 2 3 68 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 136 166 (accept_3_3 5 136 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 136 166 2 2 68 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 136 166 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 136 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 136 166 2 1 68 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 136 166 (Polychromatic418967fa.accept_7_1_3_5_1_33 1
  136 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 136 166)))))))))))))))))))))))))))))))
  (allB_succ' 32 135 166 (Eq.refl Bool.true) (allA_succ_of_accept 31 135 166 (Polychromatic418967fa.accept_6_1_3_4_1_1
  31 135 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 135 166
  (Polychromatic418967fa.accept_12_6_3_10_1_224 30 135 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 135 166 (accept_3_3 29 135 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 135 166 (Polychromatic418967fa.accept_13_2_5_10_1_250 28 135 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 135 166 (Polychromatic418967fa.accept_19_8_2_14_1_3640 27 135 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 135 166 (accept_3_3 26 135 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 135 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 135 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 135 166
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 135 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 135 166 (accept_3_3 23 135 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 135 166 (Polychromatic418967fa.accept_25_22_10_16_1_9222 22 135 166 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 135 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 135 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 135 166 (accept_3_3 20 135 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 135 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 135 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 135 166
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 135 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 135 166 (accept_3_3 17 135 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 135 166 (Polychromatic418967fa.accept_19_16_2_14_1_9221 16 135 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 135 166 (Polychromatic418967fa.accept_13_2_5_10_1_250 15 135 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 135 166 (accept_3_3 14 135 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 135 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 135 166
  (Polychromatic418967fa.accept_17_12_16_13_1_7951 12 135 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 135 166 (accept_3_3 11 135 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 135 166 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 135 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 135 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 135 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 135 166 (accept_3_3 8 135 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 7
  135 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 135 166
  (Polychromatic418967fa.accept_12_6_3_10_1_224 6 135 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 135 166 (accept_3_3 5 135 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  135 166 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 135 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 135 166 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 135 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 135 166 (accept_3_3 2 135 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 135 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135 166)))))))))))))))))))))))))))))))) (allB_succ' 33
  134 166 (Eq.refl Bool.true) (allA_of_3_1 33 134 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 133 166
  (Eq.refl Bool.true) (allA_succ_of_accept 33 133 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 133 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 133 166 (accept_3_3 32 133 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 133 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 133 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 133 166
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 133 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 133 166 (accept_3_3 29 133 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 133 166 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 133 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 133 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 133 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 133 166 (accept_3_3 26 133 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 133 166 (Polychromatic418967fa.accept_15_10_13_1_1_3698 25 133 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 133 166
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 133 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 133 166 (accept_3_3 23 133 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 133 166 (Polychromatic418967fa.accept_21_1_7_19_1_9193 22 133 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 133 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 133 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 133 166 (accept_3_3 20 133 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 133 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 133 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 133 166
  (Polychromatic418967fa.accept_10_8_3_6_1_685 18 133 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 133 166 (accept_3_3 17 133 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 133 166 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 133 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 133 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 133 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 133 166 (accept_3_3 14 133 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 133 166 (Polychromatic418967fa.accept_18_13_7_4_1_2738 13 133 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 133 166
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 133 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 133 166 (accept_3_3 11 133 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 133 166 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 133 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 133 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 133 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 133 166 (accept_3_3 8 133 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 133 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 133 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 133 166
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 133 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 133 166 (accept_3_3 5 133 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  133 166 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 133 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 133 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 133 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 133 166 (accept_3_3 2 133 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 133 166 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 133 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 133 166)))))))))))))))))))))))))))))))))) (allB_succ' 35
  132 166 (Eq.refl Bool.true) (allA_succ_of_gcd 34 132 166 2 17 66 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 132 166 (Polychromatic418967fa.accept_18_15_6_4_1_5147 33 132
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 132 166 2 16 66 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 132 166
  (Polychromatic418967fa.accept_10_1_2_6_1_638 31 132 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 132 166 2 15 66 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 132 166 (accept_3_3 29 132 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 132 166 2 14 66 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 132 166 (Polychromatic418967fa.accept_14_13_6_12_1_3126 27 132 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 132 166 2 13 66 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 132 166
  (Polychromatic418967fa.accept_7_4_6_5_1_141 25 132 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 132 166 2 12 66 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 132 166 (accept_3_3 23 132 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 132 166 2 11 66 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 132 166 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 132 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 132 166 2 10 66 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 132 166
  (Polychromatic418967fa.accept_9_1_6_4_1_49 19 132 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 132 166 2 9 66 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 132 166 (accept_3_3 17 132 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  132 166 2 8 66 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 132 166 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 132 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 132 166 2 7 66 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 132 166 (Polychromatic418967fa.accept_14_13_6_12_1_3126 13 132 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 132 166 2 6 66 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 132 166 (accept_3_3 11
  132 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 132 166 2 5 66 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 132 166
  (Polychromatic418967fa.accept_25_9_7_16_1_9220 9 132 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 132 166 2 4 66 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 132 166 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 132 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132 166 2 3 66 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 132 166 (accept_3_3 5 132 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 132 166 2 2 66 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 132 166 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 132 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 132 166 2 1 66 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 132 166 (Polychromatic418967fa.accept_7_1_6_5_1_39 1
  132 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132
  166))))))))))))))))))))))))))))))))))) (allB_succ' 36 131 166 (Eq.refl Bool.true) (allA_of_3_1 36 131 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 130 166 (Eq.refl Bool.true) (allA_succ_of_gcd 36 130 166 2 18 65 83
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 130 166
  (accept_3_3 35 130 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 130 166 2 17 65 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 130 166
  (Polychromatic418967fa.accept_16_1_2_6_1_2295 33 130 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 130 166 2 16 65 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 130 166 (Polychromatic418967fa.accept_19_12_16_14_1_3661 31 130 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 130 166 2 15 65 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 130 166 (accept_3_3 29 130 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 130 166 2 14 65 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 130 166
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 130 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 130 166 2 13 65 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 130 166 (Polychromatic418967fa.accept_16_9_2_6_1_4434 25 130 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 130 166 2 12 65 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 130 166 (accept_3_3 23 130 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 130 166 2 11 65 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 130 166
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 21 130 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 130 166 2 10 65 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 130 166 (Polychromatic418967fa.accept_16_3_2_6_1_4461 19 130 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 130 166 2 9 65 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 130 166 (accept_3_3 17 130 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 130 166 2 8 65 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 130 166
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 130 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 130 166 2 7 65 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 130 166 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 130 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 130 166 2 6 65 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 130 166 (accept_3_3 11 130 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 130 166 2 5 65 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 130 166 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 130 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 130 166 2 4 65 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 130 166
  (Polychromatic418967fa.accept_15_7_10_1_1_1836 7 130 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 130 166 2 3 65 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 130 166 (accept_3_3 5 130 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 130
  166 2 2 65 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  130 166 (Polychromatic418967fa.accept_16_3_2_6_1_4461 3 130 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 130 166 2 1 65 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 130 166 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 130 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 130 166))))))))))))))))))))))))))))))))))))) (allB_succ' 38 129 166
  (Eq.refl Bool.true) (allA_succ_of_accept 37 129 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 129 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 129 166
  (Polychromatic418967fa.accept_7_1_3_5_1_33 36 129 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 129 166 (accept_3_3 35 129 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 129 166 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 129 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 129 166 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 129 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 129 166 (accept_3_3 32 129 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 129 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 129 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 129 166
  (Polychromatic418967fa.accept_7_2_3_5_1_34 30 129 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 129 166 (accept_3_3 29 129 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 129 166 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 129 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 129 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 129 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 129 166 (accept_3_3 26 129 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 129 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 129 166
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 129 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 129 166 (accept_3_3 23 129 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 129 166 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 129 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 129 166 (Polychromatic418967fa.accept_13_8_12_10_1_4414 21 129 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 129 166 (accept_3_3 20 129 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 129 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 129 166
  (Polychromatic418967fa.accept_12_6_9_10_1_565 18 129 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 129 166 (accept_3_3 17 129 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 129 166 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 129 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 129 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 129 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 129 166 (accept_3_3 14 129 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 129 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 129 166
  (Polychromatic418967fa.accept_25_12_4_16_1_9219 12 129 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 129 166 (accept_3_3 11 129 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 129 166 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 129 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 129 166 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 129 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 129 166 (accept_3_3 8 129 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 7
  129 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 129 166
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 129 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 129 166 (accept_3_3 5 129 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  129 166 (Polychromatic418967fa.accept_11_4_8_1_1_1047 4 129 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 129 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 129 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 129 166 (accept_3_3 2 129 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 129 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129 166))))))))))))))))))))))))))))))))))))))
  (allB_succ' 39 128 166 (Eq.refl Bool.true) (allA_of_3_1 39 128 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 40 127 166 (Eq.refl Bool.true) (allA_succ_of_accept 39 127 166 (Polychromatic418967fa.accept_6_3_1_4_1_25
  39 127 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 127 166 (accept_3_3 38
  127 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 127 166
  (Polychromatic418967fa.accept_4_1_3_2_1_3 37 127 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 127 166 (Polychromatic418967fa.accept_15_6_7_1_1_93 36 127 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 127 166 (accept_3_3 35 127 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 127 166 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 127 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 127 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 33
  127 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 127 166 (accept_3_3 32
  127 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 127 166
  (Polychromatic418967fa.accept_7_3_1_5_1_44 31 127 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 127 166 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 127 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 127 166 (accept_3_3 29 127 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 127 166 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 127 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 127 166
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 127 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 127 166 (accept_3_3 26 127 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 127 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 127 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 127 166 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 127 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 127 166 (accept_3_3 23 127 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 127 166 (Polychromatic418967fa.accept_17_5_8_13_1_7994 22 127 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 127 166
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 127 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 127 166 (accept_3_3 20 127 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 127 166 (Polychromatic418967fa.accept_20_19_7_6_1_6255 19 127 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 127 166 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 127 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 127 166 (accept_3_3 17 127 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 127 166 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 127 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 127 166
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 127 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 127 166 (accept_3_3 14 127 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 127 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 127 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 127 166 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 127 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 127 166 (accept_3_3 11 127 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 127 166 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 127 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 127 166
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 127 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 127 166 (accept_3_3 8 127 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  127 166 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 127 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 127 166 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 127 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 127 166 (accept_3_3 5 127 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 127 166 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 127 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 127 166
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 127 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 127 166 (accept_3_3 2 127 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  127 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 127 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 127 166)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 126 166 (Eq.refl Bool.true)
  (allA_succ_of_gcd 40 126 166 2 20 63 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 126 166 (Polychromatic418967fa.accept_11_6_5_1_1_586 39 126 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 126 166 2 19 63 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 126 166
  (Polychromatic418967fa.accept_15_7_6_1_1_1091 37 126 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 126 166 2 18 63 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 126 166 (accept_3_3 35 126 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 126 166 2 17 63 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 126 166 (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 126 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 126 166 2 16 63 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 126 166
  (Polychromatic418967fa.accept_23_8_11_5_1_9218 31 126 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 126 166 2 15 63 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 126 166 (accept_3_3 29 126 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 126 166 2 14 63 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 126 166 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 126 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 126 166 2 13 63 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 126 166
  (Polychromatic418967fa.accept_13_12_9_10_1_1223 25 126 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 126 166 2 12 63 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 126 166 (accept_3_3 23 126 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 126 166 2 11 63 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 126 166 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 126 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 126 166 2 10 63 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 126 166
  (Polychromatic418967fa.accept_13_6_9_10_1_1201 19 126 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 126 166 2 9 63 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 126 166 (accept_3_3 17 126 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  126 166 2 8 63 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 126 166 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 126 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 126 166 2 7 63 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 126 166 (Polychromatic418967fa.accept_19_13_12_14_1_9217 13 126 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 126 166 2 6 63 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 126 166 (accept_3_3 11
  126 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 126 166 2 5 63 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 126 166
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 126 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 126 166 2 4 63 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 126 166 (Polychromatic418967fa.accept_15_7_6_1_1_1091 7 126 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 126 166 2 3 63 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 126 166 (accept_3_3 5 126 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 126 166 2 2 63 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 126 166 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 126 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 126 166 2 1 63 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 126 166 (Polychromatic418967fa.accept_13_1_9_10_1_625 1
  126 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  166))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 125 166 (Eq.refl Bool.true) (allA_of_3_1 42 125 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 124 166 (Eq.refl Bool.true) (allA_succ_of_gcd 42 124 166 2 21
  62 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 124 166
  (accept_3_3 41 124 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 124 166 2 20 62 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 124 166
  (Polychromatic418967fa.accept_9_3_7_4_1_53 39 124 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 124 166 2 19 62 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 124 166 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 124 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 124 166 2 18 62 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 124 166 (accept_3_3 35 124 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 124 166 2 17 62 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 124 166 (Polychromatic418967fa.accept_9_6_7_4_1_212 33
  124 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 124 166 2 16 62 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 124 166
  (Polychromatic418967fa.accept_12_7_4_10_1_572 31 124 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 124 166 2 15 62 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 124 166 (accept_3_3 29 124 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 124 166 2 14 62 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 124 166 (Polychromatic418967fa.accept_15_12_4_1_1_3746 27 124 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 124 166 2 13 62 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 124 166
  (Polychromatic418967fa.accept_10_5_4_6_1_319 25 124 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 124 166 2 12 62 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 124 166 (accept_3_3 23 124 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 124 166 2 11 62 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 124 166 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 124 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 124 166 2 10 62 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 124 166
  (Polychromatic418967fa.accept_9_1_7_4_1_52 19 124 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 124 166 2 9 62 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 124 166 (accept_3_3 17 124 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  124 166 2 8 62 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 124 166 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 124 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 124 166 2 7 62 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 124 166 (Polychromatic418967fa.accept_11_2_3_1_1_244 13 124 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 124 166 2 6 62 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 124 166 (accept_3_3 11 124 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 124 166 2 5 62 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 124 166
  (Polychromatic418967fa.accept_17_9_5_13_1_2033 9 124 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 124 166 2 4 62 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 124 166 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 124 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 124 166 2 3 62 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 124 166 (accept_3_3 5 124 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 124 166 2 2 62 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 124 166 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 124 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 124 166 2 1 62 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 124 166 (Polychromatic418967fa.accept_9_1_7_4_1_52 1
  124 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 124
  166))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 123 166 (Eq.refl Bool.true) (allA_succ_of_accept 43 123
  166 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 123 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 123 166 (Polychromatic418967fa.accept_12_6_3_10_1_224 42 123 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 123 166 (accept_3_3 41 123 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 123 166 (Polychromatic418967fa.accept_54_40_15_4_1_9216 40 123 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 123 166
  (Polychromatic418967fa.accept_9_3_6_4_1_210 39 123 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 123 166 (accept_3_3 38 123 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 123 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 123 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 123 166 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 123 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 123 166 (accept_3_3 35 123 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 123 166 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 123 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 123 166
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 123 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 123 166 (accept_3_3 32 123 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 123 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 123 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 123 166 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 123 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 123 166 (accept_3_3 29 123 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 123 166 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 123 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 123 166
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 123 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 123 166 (accept_3_3 26 123 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 123 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 123 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 123 166 (Polychromatic418967fa.accept_18_6_15_4_1_3916 24 123 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 123 166 (accept_3_3 23 123 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 123 166 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 123 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 123 166
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 123 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 123 166 (accept_3_3 20 123 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 123 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 123 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 123 166 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 123 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 123 166 (accept_3_3 17 123 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 123 166 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 123 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 123 166
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 123 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 123 166 (accept_3_3 14 123 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 123 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 123 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 123 166 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 123 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 123 166 (accept_3_3 11 123 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 123 166 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 123 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 123 166
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 123 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 123 166 (accept_3_3 8 123 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  123 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 123 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 123 166 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 123 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 123 166 (accept_3_3 5 123 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 166 (Polychromatic418967fa.accept_13_4_6_10_1_1199 4 123 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 123 166
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 123 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 123 166 (accept_3_3 2 123 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  123 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 123 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 123 166)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 122 166 (Eq.refl Bool.true)
  (allA_of_3_1 45 122 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 46 121 166 (Eq.refl Bool.true)
  (allA_succ_of_accept 45 121 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 121 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 121 166 (accept_3_3 44 121 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 121 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 121 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 121 166 (Polychromatic418967fa.accept_10_2_1_6_1_634
  42 121 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 121 166 (accept_3_3 41
  121 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 121 166
  (Polychromatic418967fa.accept_12_4_1_10_1_221 40 121 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 121 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 121 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 121 166 (accept_3_3 38 121 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 121 166 (Polychromatic418967fa.accept_10_7_1_6_1_673 37 121 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 121 166
  (Polychromatic418967fa.accept_20_16_1_6_1_6196 36 121 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 121 166 (accept_3_3 35 121 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 121 166 (Polychromatic418967fa.accept_13_8_4_10_1_4358 34 121 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 121 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 121 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 121 166 (accept_3_3 32 121 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 121 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 121 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 121 166
  (Polychromatic418967fa.accept_19_11_7_14_1_6394 30 121 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 121 166 (accept_3_3 29 121 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 121 166 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 121 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 121 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 121 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 121 166 (accept_3_3 26 121 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 121 166 (Polychromatic418967fa.accept_7_4_2_5_1_527
  25 121 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 121 166
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 121 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 121 166 (accept_3_3 23 121 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 121 166 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 121 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 121 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 121 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 121 166 (accept_3_3 20 121 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 121 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 121 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 121 166
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 121 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 121 166 (accept_3_3 17 121 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 121 166 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 121 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 121 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 121 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 121 166 (accept_3_3 14 121 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 121 166 (Polychromatic418967fa.accept_16_13_9_6_1_2306 13 121 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 121 166
  (Polychromatic418967fa.accept_10_2_1_6_1_634 12 121 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 121 166 (accept_3_3 11 121 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 121 166 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 121 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 121 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 121 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 121 166 (accept_3_3 8 121 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 121 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 121 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 121 166
  (Polychromatic418967fa.accept_13_6_4_10_1_660 6 121 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 121 166 (accept_3_3 5 121 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  121 166 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 121 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 121 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 121 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 121 166 (accept_3_3 2 121 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 121 166 (Polychromatic418967fa.accept_13_1_4_10_1_622 1 121 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 121 166))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 47 120 166 (Eq.refl Bool.true) (allA_succ_of_gcd 46 120 166 2 23 60 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 120 166
  (Polychromatic418967fa.accept_7_3_1_5_1_44 45 120 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 120 166 2 22 60 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 120 166 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 120 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 120 166 2 21 60 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 120 166 (accept_3_3 41 120 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 120 166 2 20 60 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 120 166 (Polychromatic418967fa.accept_7_4_1_5_1_540 39
  120 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 120 166 2 19 60 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 120 166
  (Polychromatic418967fa.accept_9_1_3_4_1_47 37 120 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 120 166 2 18 60 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 120 166 (accept_3_3 35 120 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 120 166 2 17 60 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 120 166 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 120 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 120 166 2 16 60 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 120 166
  (Polychromatic418967fa.accept_7_3_1_5_1_44 31 120 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 120 166 2 15 60 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 120 166 (accept_3_3 29 120 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 120 166 2 14 60 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 120 166 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 120 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 120 166 2 13 60 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 120 166
  (Polychromatic418967fa.accept_7_4_1_5_1_540 25 120 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 120 166 2 12 60 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 120 166 (accept_3_3 23 120 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 120 166 2 11 60 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 120 166 (Polychromatic418967fa.accept_25_21_20_16_1_9215 21 120 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 120 166 2 10 60 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 120 166
  (Polychromatic418967fa.accept_9_1_3_4_1_47 19 120 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 120 166 2 9 60 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 120 166 (accept_3_3 17 120 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  120 166 2 8 60 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 120 166 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 120 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 120 166 2 7 60 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 120 166 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 120 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 166 2 6 60 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 166 (accept_3_3 11 120 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 120 166 2 5 60 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 120 166
  (Polychromatic418967fa.accept_11_9_10_1_1_581 9 120 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 120 166 2 4 60 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 120 166 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 120 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120 166 2 3 60 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 120 166 (accept_3_3 5 120 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 120 166 2 2 60 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 120 166 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 120 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 120 166 2 1 60 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 120 166 (Polychromatic418967fa.accept_9_1_3_4_1_47 1
  120 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  166))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 119 166 (Eq.refl Bool.true) (allA_of_3_1 48 119 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 118 166 (Eq.refl Bool.true) (allA_succ_of_gcd 48 118 166 2 24
  59 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 118 166
  (accept_3_3 47 118 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 118 166 2 23 59 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 118 166
  (Polychromatic418967fa.accept_19_7_4_14_1_5003 45 118 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 118 166 2 22 59 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 118 166 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 118 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 118 166 2 21 59 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 118 166 (accept_3_3 41 118 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 118 166 2 20 59 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 118 166 (Polychromatic418967fa.accept_7_4_6_5_1_141 39
  118 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 118 166 2 19 59 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 118 166
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 37 118 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 118 166 2 18 59 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 118 166 (accept_3_3 35 118 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 118 166 2 17 59 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 118 166 (Polychromatic418967fa.accept_9_6_1_4_1_474 33 118 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 118 166 2 16 59 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 118 166
  (Polychromatic418967fa.accept_18_13_10_4_1_5150 31 118 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 118 166 2 15 59 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 118 166 (accept_3_3 29 118 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 118 166 2 14 59 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 118 166 (Polychromatic418967fa.accept_14_13_6_12_1_3126 27 118 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 118 166 2 13 59 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 118 166
  (Polychromatic418967fa.accept_7_4_6_5_1_141 25 118 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 118 166 2 12 59 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 118 166 (accept_3_3 23 118 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 118 166 2 11 59 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 118 166 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 118 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 118 166 2 10 59 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 118 166
  (Polychromatic418967fa.accept_25_19_18_16_1_9214 19 118 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 118 166 2 9 59 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 118 166 (accept_3_3 17 118 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 118 166 2 8 59 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 118 166 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 118 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 118 166 2 7 59 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 118 166 (Polychromatic418967fa.accept_10_3_8_6_1_326
  13 118 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 118 166 2 6 59 83
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 118 166
  (accept_3_3 11 118 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 118 166 2 5 59 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 118 166
  (Polychromatic418967fa.accept_13_9_1_10_1_647 9 118 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 118 166 2 4 59 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 118 166 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 118 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 118 166 2 3 59 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 118 166 (accept_3_3 5 118 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 118 166 2 2 59 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 118 166 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 118 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 118 166 2 1 59 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 118 166 (Polychromatic418967fa.accept_7_1_6_5_1_39 1
  118 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118
  166))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 117 166 (Eq.refl Bool.true) (allA_succ_of_accept
  49 117 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 117 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 117 166 (Polychromatic418967fa.accept_18_12_9_4_1_2740 48 117 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 117 166 (accept_3_3 47 117 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 117 166 (Polychromatic418967fa.accept_19_8_3_14_1_3571 46 117
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 117 166
  (Polychromatic418967fa.accept_14_3_5_12_1_4000 45 117 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 117 166 (accept_3_3 44 117 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 117 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 117 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 117 166 (Polychromatic418967fa.accept_12_6_9_10_1_565 42 117 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 117 166 (accept_3_3 41 117 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 117 166 (Polychromatic418967fa.accept_22_18_7_12_1_9213 40 117
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 117 166
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 117 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 117 166 (accept_3_3 38 117 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 117 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 117 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 117 166 (Polychromatic418967fa.accept_16_4_5_6_1_8071 36 117 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 117 166 (accept_3_3 35 117 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 166 (Polychromatic418967fa.accept_15_4_12_1_1_1081 34 117
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 117 166
  (Polychromatic418967fa.accept_10_3_7_6_1_659 33 117 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 117 166 (accept_3_3 32 117 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 117 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 117 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 117 166 (Polychromatic418967fa.accept_12_6_9_10_1_565 30 117 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 117 166 (accept_3_3 29 117 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 166 (Polychromatic418967fa.accept_11_6_7_1_1_564 28 117
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 117 166
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 117 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 117 166 (accept_3_3 26 117 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 117 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 117 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 117 166 (Polychromatic418967fa.accept_14_10_5_12_1_3995 24 117 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 117 166 (accept_3_3 23 117 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 166 (Polychromatic418967fa.accept_17_5_15_13_1_7936 22 117
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 117 166
  (Polychromatic418967fa.accept_10_1_7_6_1_91 21 117 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 117 166 (accept_3_3 20 117 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 117 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 117 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 117 166 (Polychromatic418967fa.accept_12_6_9_10_1_565 18 117 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 117 166 (accept_3_3 17 117 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 166 (Polychromatic418967fa.accept_19_16_3_14_1_9212 16 117
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 117 166
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 117 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 117 166 (accept_3_3 14 117 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 117 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 117 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 117 166 (Polychromatic418967fa.accept_18_12_9_4_1_2740 12 117 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 117 166 (accept_3_3 11 117 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 166 (Polychromatic418967fa.accept_14_10_5_12_1_3995 10 117
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 166
  (Polychromatic418967fa.accept_19_9_3_14_1_2400 9 117 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 117 166 (accept_3_3 8 117 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  117 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 117 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 117 166 (Polychromatic418967fa.accept_11_6_7_1_1_564 6 117 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 117 166 (accept_3_3 5 117 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 166 (Polychromatic418967fa.accept_15_4_12_1_1_1081 4 117 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 117 166
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 117 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 117 166 (accept_3_3 2 117 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  117 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 117 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 117 166)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 116 166 (Eq.refl
  Bool.true) (allA_of_3_1 51 116 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 52 115 166 (Eq.refl Bool.true)
  (allA_succ_of_accept 51 115 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 115 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 115 166 (accept_3_3 50 115 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 115 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 115 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 115 166 (Polychromatic418967fa.accept_9_3_7_4_1_53 48
  115 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 115 166 (accept_3_3 47
  115 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 115 166
  (Polychromatic418967fa.accept_9_1_7_4_1_52 46 115 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 115 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 115 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 115 166 (accept_3_3 44 115 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 115 166 (Polychromatic418967fa.accept_7_1_3_5_1_33 43 115 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 115 166 (Polychromatic418967fa.accept_9_6_7_4_1_212
  42 115 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 115 166 (accept_3_3 41
  115 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 115 166
  (Polychromatic418967fa.accept_12_4_7_10_1_563 40 115 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 115 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 115 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 115 166 (accept_3_3 38 115 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 115 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 115 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 115 166 (Polychromatic418967fa.accept_7_1_3_5_1_33 36
  115 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 115 166 (accept_3_3 35
  115 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 115 166
  (Polychromatic418967fa.accept_10_4_5_6_1_651 34 115 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 115 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 115 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 115 166 (accept_3_3 32 115 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 115 166 (Polychromatic418967fa.accept_10_1_5_6_1_649 31 115 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 115 166
  (Polychromatic418967fa.accept_7_2_3_5_1_34 30 115 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 115 166 (accept_3_3 29 115 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 115 166 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 115 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 115 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 115 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 115 166 (accept_3_3 26 115 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 115 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 115 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 115 166
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 115 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 115 166 (accept_3_3 23 115 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 115 166 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 115 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 115 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 115 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 115 166 (accept_3_3 20 115 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 115 166 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 115 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 115 166
  (Polychromatic418967fa.accept_16_2_3_6_1_3372 18 115 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 115 166 (accept_3_3 17 115 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 115 166 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 115 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 115 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 115 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 115 166 (accept_3_3 14 115 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 115 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 115 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 115 166
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 115 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 115 166 (accept_3_3 11 115 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 115 166 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 115 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 115 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 115 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 115 166 (accept_3_3 8 115 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 115 166 (Polychromatic418967fa.accept_15_7_10_1_1_1836 7 115 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 115 166
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 115 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 115 166 (accept_3_3 5 115 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  115 166 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 115 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 115 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 115 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 166 (accept_3_3 2 115 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 115 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 115 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115
  166)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 114 166 (Eq.refl Bool.true) (allA_succ_of_gcd
  52 114 166 2 26 57 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 114 166 (Polychromatic418967fa.accept_12_3_6_10_1_576 51 114 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 114 166 2 25 57 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 114 166 (Polychromatic418967fa.accept_14_7_2_12_1_1430
  49 114 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 114 166 2 24 57 83
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 114 166
  (accept_3_3 47 114 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 114 166 2 23 57 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 114 166
  (Polychromatic418967fa.accept_7_3_2_5_1_147 45 114 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 114 166 2 22 57 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 114 166 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 114 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 114 166 2 21 57 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 114 166 (accept_3_3 41 114 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 114 166 2 20 57 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 114 166 (Polychromatic418967fa.accept_7_4_2_5_1_527 39
  114 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 114 166 2 19 57 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 114 166
  (Polychromatic418967fa.accept_9_1_6_4_1_49 37 114 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 114 166 2 18 57 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 114 166 (accept_3_3 35 114 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 114 166 2 17 57 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 114 166 (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 114 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 114 166 2 16 57 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 114 166
  (Polychromatic418967fa.accept_7_3_2_5_1_147 31 114 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 114 166 2 15 57 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 114 166 (accept_3_3 29 114 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 114 166 2 14 57 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 114 166 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 114 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 114 166 2 13 57 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 114 166
  (Polychromatic418967fa.accept_7_4_2_5_1_527 25 114 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 114 166 2 12 57 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 114 166 (accept_3_3 23 114 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 114 166 2 11 57 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 114 166 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 114 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 114 166 2 10 57 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 114 166
  (Polychromatic418967fa.accept_9_1_6_4_1_49 19 114 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 166 2 9 57 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 114 166 (accept_3_3 17 114 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  114 166 2 8 57 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 114 166 (Polychromatic418967fa.accept_10_5_4_6_1_319 15 114 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 114 166 2 7 57 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 114 166 (Polychromatic418967fa.accept_22_13_4_12_1_9211 13 114 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 114 166 2 6 57 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 114 166 (accept_3_3 11
  114 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 114 166 2 5 57 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 114 166
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 114 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 114 166 2 4 57 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 114 166 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 114 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114 166 2 3 57 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 114 166 (accept_3_3 5 114 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 114 166 2 2 57 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 114 166 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 114 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 114 166 2 1 57 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 166 (Polychromatic418967fa.accept_9_1_6_4_1_49 1
  114 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  166))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 113 166 (Eq.refl Bool.true) (allA_of_3_1 54
  113 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 55 112 166 (Eq.refl Bool.true) (allA_succ_of_gcd 54 112
  166 2 27 56 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  112 166 (accept_3_3 53 112 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 112 166 2 26 56 83
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 112 166
  (Polychromatic418967fa.accept_10_1_2_6_1_638 51 112 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 112 166 2 25 56 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 112 166 (Polychromatic418967fa.accept_12_1_4_10_1_209 49 112 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 112 166 2 24 56 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 112 166 (accept_3_3 47 112 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 112 166 2 23 56 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 112 166
  (Polychromatic418967fa.accept_20_5_12_6_1_7806 45 112 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 112 166 2 22 56 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 112 166 (Polychromatic418967fa.accept_11_10_2_1_1_1036 43 112 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 112 166 2 21 56 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 112 166 (accept_3_3 41 112 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 112 166 2 20 56 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 112 166
  (Polychromatic418967fa.accept_15_9_7_1_1_1075 39 112 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 112 166 2 19 56 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 112 166 (Polychromatic418967fa.accept_12_1_4_10_1_209 37 112 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 112 166 2 18 56 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 112 166 (accept_3_3 35 112 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 112 166 2 17 56 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 112 166
  (Polychromatic418967fa.accept_13_7_8_10_1_2663 33 112 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 112 166 2 16 56 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 112 166 (Polychromatic418967fa.accept_10_1_2_6_1_638 31 112 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 112 166 2 15 56 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 112 166 (accept_3_3 29 112 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 112 166 2 14 56 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 112 166 (Polychromatic418967fa.accept_20_7_12_6_1_2164
  27 112 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 112 166 2 13 56 83
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 112 166
  (Polychromatic418967fa.accept_11_3_2_1_1_994 25 112 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 112 166 2 12 56 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 112 166 (accept_3_3 23 112 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 112 166 2 11 56 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 112 166 (Polychromatic418967fa.accept_10_1_2_6_1_638 21 112 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 112 166 2 10 56 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 112 166
  (Polychromatic418967fa.accept_12_7_4_10_1_572 19 112 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 112 166 2 9 56 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 112 166 (accept_3_3 17 112 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  112 166 2 8 56 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 112 166 (Polychromatic418967fa.accept_13_2_8_10_1_1902 15 112 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 112 166 2 7 56 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 112 166 (Polychromatic418967fa.accept_12_1_4_10_1_209 13 112 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 112 166 2 6 56 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 112 166 (accept_3_3 11 112 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 112 166 2 5 56 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 112 166
  (Polychromatic418967fa.accept_15_9_7_1_1_1075 9 112 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 112 166 2 4 56 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 112 166 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 112 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 112 166 2 3 56 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 112 166 (accept_3_3 5 112 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 112 166 2 2 56 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 112 166 (Polychromatic418967fa.accept_11_3_2_1_1_994 3 112 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 112 166 2 1 56 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 112 166 (Polychromatic418967fa.accept_10_1_2_6_1_638 1
  112 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112
  166))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 111 166 (Eq.refl Bool.true)
  (allA_succ_of_accept 55 111 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 111 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 111 166 (Polychromatic418967fa.accept_12_6_3_10_1_224 54 111
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 111 166 (accept_3_3 53 111
  166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 111 166
  (Polychromatic418967fa.accept_9_7_3_4_1_218 52 111 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 111 166 (Polychromatic418967fa.accept_9_6_3_4_1_477 51 111 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 111 166 (accept_3_3 50 111 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 111 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 111 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 111 166
  (Polychromatic418967fa.accept_14_6_13_12_1_810 48 111 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 111 166 (accept_3_3 47 111 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 111 166 (Polychromatic418967fa.accept_7_4_6_5_1_141 46 111 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 111 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 111 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 111 166 (accept_3_3 44 111 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 111 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 111 166
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 111 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 111 166 (accept_3_3 41 111 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 111 166 (Polychromatic418967fa.accept_15_10_6_1_1_3707 40 111 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 111 166 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 111 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 111 166 (accept_3_3 38 111 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 111 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 111 166
  (Polychromatic418967fa.accept_7_1_6_5_1_39 36 111 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 111 166 (accept_3_3 35 111 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 111 166 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 111 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 111 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 111 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 111 166 (accept_3_3 32 111 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 111 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 111 166
  (Polychromatic418967fa.accept_12_6_3_10_1_224 30 111 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 111 166 (accept_3_3 29 111 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 111 166 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 111 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 111 166 (Polychromatic418967fa.accept_10_7_1_6_1_673 27 111 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 111 166 (accept_3_3 26 111 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 111 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 166
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 111 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 111 166 (accept_3_3 23 111 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 111 166 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 111 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 111 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 111 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 111 166 (accept_3_3 20 111 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 111 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 166
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 111 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 111 166 (accept_3_3 17 111 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 111 166 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 111 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 111 166 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 111 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 111 166 (accept_3_3 14 111 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 111 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 166
  (Polychromatic418967fa.accept_10_2_1_6_1_634 12 111 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 111 166 (accept_3_3 11 111 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 111 166 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 111 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 111 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 111 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 166 (accept_3_3 8 111 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 111 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 166
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 111 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 111 166 (accept_3_3 5 111 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  111 166 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 111 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 111 166 (Polychromatic418967fa.accept_13_3_7_10_1_668 3 111 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 166 (accept_3_3 2 111 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 111 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111
  166)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 110 166 (Eq.refl Bool.true) (allA_of_3_1 57
  110 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 58 109 166 (Eq.refl Bool.true) (allA_succ_of_accept 57
  109 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 109 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 109 166 (accept_3_3 56 109 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 109 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 109 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 109 166 (Polychromatic418967fa.accept_13_2_5_10_1_250 54 109
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 109 166 (accept_3_3 53 109
  166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 109 166
  (Polychromatic418967fa.accept_9_7_1_4_1_217 52 109 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 109 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 109 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 109 166 (accept_3_3 50 109 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 109 166 (Polychromatic418967fa.accept_21_7_4_19_1_4525 49 109 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 109 166
  (Polychromatic418967fa.accept_7_6_4_5_1_314 48 109 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 109 166 (accept_3_3 47 109 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 109 166 (Polychromatic418967fa.accept_11_2_10_1_1_1017 46 109 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 109 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 109 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 109 166 (accept_3_3 44 109 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 109 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 109 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 109 166
  (Polychromatic418967fa.accept_9_6_1_4_1_474 42 109 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 109 166 (accept_3_3 41 109 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 109 166 (Polychromatic418967fa.accept_12_4_1_10_1_221 40 109 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 109 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 109 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 109 166 (accept_3_3 38 109 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 109 166 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 109 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 109 166
  (Polychromatic418967fa.accept_7_1_4_5_1_35 36 109 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 109 166 (accept_3_3 35 109 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 109 166 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 109 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 109 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 109 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 109 166 (accept_3_3 32 109 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 109 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 109 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 109 166
  (Polychromatic418967fa.accept_7_2_4_5_1_313 30 109 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 109 166 (accept_3_3 29 109 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 109 166 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 109 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 109 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 109 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 109 166 (accept_3_3 26 109 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 109 166 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 109 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 109 166
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 109 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 109 166 (accept_3_3 23 109 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 109 166 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 109 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 109 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 109 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 109 166 (accept_3_3 20 109 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 109 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 109 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 109 166
  (Polychromatic418967fa.accept_15_3_4_1_1_1072 18 109 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 109 166 (accept_3_3 17 109 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 109 166 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 109 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 109 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 109 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 109 166 (accept_3_3 14 109 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 109 166 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 109 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 109 166
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 109 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 109 166 (accept_3_3 11 109 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 109 166 (Polychromatic418967fa.accept_20_10_9_6_1_6164 10 109 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 109 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 109 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 109 166 (accept_3_3 8 109 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 109 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 109 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 109 166
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 109 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 109 166 (accept_3_3 5 109 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  109 166 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 109 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 109 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 109 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 109 166 (accept_3_3 2 109 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 109 166 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 109 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 109
  166)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 108 166 (Eq.refl Bool.true)
  (allA_succ_of_gcd 58 108 166 2 29 54 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 108 166 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 108 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 108 166 2 28 54 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 108 166
  (Polychromatic418967fa.accept_23_9_16_5_1_7482 55 108 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 108 166 2 27 54 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 108 166 (accept_3_3 53 108 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 108 166 2 26 54 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 108 166 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 108 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 108 166 2 25 54 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 108 166
  (Polychromatic418967fa.accept_15_4_3_1_1_487 49 108 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 108 166 2 24 54 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 108 166 (accept_3_3 47 108 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 108 166 2 23 54 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 108 166 (Polychromatic418967fa.accept_13_6_4_10_1_660 45 108 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 108 166 2 22 54 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 108 166
  (Polychromatic418967fa.accept_7_1_3_5_1_33 43 108 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 108 166 2 21 54 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 108 166 (accept_3_3 41 108 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 108 166 2 20 54 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 108 166 (Polychromatic418967fa.accept_19_1_13_14_1_3509 39 108 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 108 166 2 19 54 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 108 166
  (Polychromatic418967fa.accept_7_2_3_5_1_34 37 108 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 108 166 2 18 54 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 108 166 (accept_3_3 35 108 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 108 166 2 17 54 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 108 166 (Polychromatic418967fa.accept_10_3_8_6_1_326 33 108 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 108 166 2 16 54 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 108 166
  (Polychromatic418967fa.accept_13_5_4_10_1_1244 31 108 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 108 166 2 15 54 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 108 166 (accept_3_3 29 108 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 108 166 2 14 54 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 108 166 (Polychromatic418967fa.accept_13_1_4_10_1_622 27 108 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 108 166 2 13 54 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 108 166
  (Polychromatic418967fa.accept_33_25_9_1_1_9210 25 108 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 108 166 2 12 54 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 108 166 (accept_3_3 23 108 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 108 166 2 11 54 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 108 166 (Polychromatic418967fa.accept_11_10_9_1_1_2186 21 108 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 108 166 2 10 54 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 108 166
  (Polychromatic418967fa.accept_13_6_4_10_1_660 19 108 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 108 166 2 9 54 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 108 166 (accept_3_3 17 108 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  108 166 2 8 54 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 108 166 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 108 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 108 166 2 7 54 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 108 166 (Polychromatic418967fa.accept_10_3_8_6_1_326 13 108 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 108 166 2 6 54 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 108 166 (accept_3_3 11 108 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 108 166 2 5 54 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 108 166
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 108 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 108 166 2 4 54 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 108 166 (Polychromatic418967fa.accept_13_7_4_10_1_2675 7 108 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 166 2 3 54 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 166 (accept_3_3 5 108 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 108 166 2 2 54 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 108 166 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 108 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 108 166 2 1 54 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 108 166 (Polychromatic418967fa.accept_7_1_3_5_1_33 1
  108 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  166))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 107 166 (Eq.refl Bool.true) (allA_of_3_1
  60 107 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 61 106 166 (Eq.refl Bool.true) (allA_succ_of_gcd 60
  106 166 2 30 53 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 106 166 (accept_3_3 59 106 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58
  106 166 2 29 53 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 106 166 (Polychromatic418967fa.accept_9_3_7_4_1_53 57 106 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 106 166 2 28 53 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 106 166 (Polychromatic418967fa.accept_7_6_1_5_1_322 55
  106 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 106 166 2 27 53 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 106 166 (accept_3_3 53
  106 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 106 166 2 26 53 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 106 166
  (Polychromatic418967fa.accept_9_6_7_4_1_212 51 106 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 106 166 2 25 53 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 106 166 (Polychromatic418967fa.accept_21_7_1_19_1_6021 49 106 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 106 166 2 24 53 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 106 166 (accept_3_3 47 106 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 106 166 2 23 53 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 106 166
  (Polychromatic418967fa.accept_7_3_1_5_1_44 45 106 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 106 166 2 22 53 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 106 166 (Polychromatic418967fa.accept_17_9_4_13_1_3057 43 106 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 106 166 2 21 53 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 106 166 (accept_3_3 41 106 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 106 166 2 20 53 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 106 166
  (Polychromatic418967fa.accept_7_4_1_5_1_540 39 106 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 106 166 2 19 53 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 106 166 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 106 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 106 166 2 18 53 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 106 166 (accept_3_3 35 106 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 106 166 2 17 53 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 106 166 (Polychromatic418967fa.accept_9_6_7_4_1_212 33
  106 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 106 166 2 16 53 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 106 166
  (Polychromatic418967fa.accept_7_3_1_5_1_44 31 106 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 106 166 2 15 53 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 106 166 (accept_3_3 29 106 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 106 166 2 14 53 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 106 166 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 106 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 106 166 2 13 53 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 106 166
  (Polychromatic418967fa.accept_7_4_1_5_1_540 25 106 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 106 166 2 12 53 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 106 166 (accept_3_3 23 106 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 106 166 2 11 53 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 106 166 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 106 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 106 166 2 10 53 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 106 166
  (Polychromatic418967fa.accept_9_1_7_4_1_52 19 106 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 106 166 2 9 53 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 106 166 (accept_3_3 17 106 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  106 166 2 8 53 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 106 166 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 106 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 106 166 2 7 53 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 106 166 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 106 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 106 166 2 6 53 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 106 166 (accept_3_3 11 106 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 106 166 2 5 53 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 106 166
  (Polychromatic418967fa.accept_17_9_4_13_1_3057 9 106 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 106 166 2 4 53 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 106 166 (Polychromatic418967fa.accept_18_7_16_4_1_1674 7 106 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 106 166 2 3 53 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 106 166 (accept_3_3 5 106 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 106 166 2 2 53 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 106 166 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 106 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 106 166 2 1 53 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 106 166 (Polychromatic418967fa.accept_9_1_7_4_1_52 1
  106 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106
  166))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 105 166 (Eq.refl Bool.true)
  (allA_succ_of_accept 61 105 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 105 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 105 166 (Polychromatic418967fa.accept_11_5_6_1_1_988 60 105
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 105 166 (accept_3_3 59 105
  166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 105 166
  (Polychromatic418967fa.accept_14_2_7_12_1_1485 58 105 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 105 166 (Polychromatic418967fa.accept_9_3_6_4_1_210 57 105 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 105 166 (accept_3_3 56 105 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 105 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 105 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 105 166 (Polychromatic418967fa.accept_10_4_5_6_1_651
  54 105 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 105 166 (accept_3_3 53
  105 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 105 166
  (Polychromatic418967fa.accept_9_7_6_4_1_483 52 105 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 105 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 105 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 105 166 (accept_3_3 50 105 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 105 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 105 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 105 166 (Polychromatic418967fa.accept_9_3_6_4_1_210
  48 105 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 105 166 (accept_3_3 47
  105 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 105 166
  (Polychromatic418967fa.accept_9_1_6_4_1_49 46 105 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 105 166 (Polychromatic418967fa.accept_16_13_9_6_1_2306 45 105 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 105 166 (accept_3_3 44 105 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 105 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 105 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 105 166 (Polychromatic418967fa.accept_12_6_9_10_1_565
  42 105 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 105 166 (accept_3_3 41
  105 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 105 166
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 40 105 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 105 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 105 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 105 166 (accept_3_3 38 105 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 105 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 105 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 105 166
  (Polychromatic418967fa.accept_22_14_17_12_1_5950 36 105 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 105 166 (accept_3_3 35 105 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 105 166 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 105 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 105 166 (Polychromatic418967fa.accept_14_5_7_12_1_4006 33 105
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 166 (accept_3_3 32 105
  166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 166
  (Polychromatic418967fa.accept_4_3_1_2_1_62 31 105 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 105 166 (Polychromatic418967fa.accept_9_3_6_4_1_210 30 105 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 105 166 (accept_3_3 29 105 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 105 166 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 105 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 105 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 27
  105 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 166 (accept_3_3 26
  105 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 166
  (Polychromatic418967fa.accept_6_1_3_4_1_1 25 105 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 105 166 (Polychromatic418967fa.accept_10_4_5_6_1_651 24 105 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 105 166 (accept_3_3 23 105 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 105 166 (Polychromatic418967fa.accept_13_9_1_10_1_647 22 105 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 105 166
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 105 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 105 166 (accept_3_3 20 105 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 105 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 105 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 105 166 (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 105 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 166 (accept_3_3 17 105 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 166 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 105 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 105 166
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 105 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 105 166 (accept_3_3 14 105 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 105 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 105 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 105 166 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 105 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 166 (accept_3_3 11 105 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 105 166 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 105 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 105 166
  (Polychromatic418967fa.accept_10_9_5_6_1_691 9 105 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 105 166 (accept_3_3 8 105 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  105 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 105 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 105 166 (Polychromatic418967fa.accept_12_6_9_10_1_565 6 105 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 105 166 (accept_3_3 5 105 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 166 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 105 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 166
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 105 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 105 166 (accept_3_3 2 105 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  105 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 105 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 105 166)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 104 166
  (Eq.refl Bool.true) (allA_of_3_1 63 104 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 64 103 166 (Eq.refl
  Bool.true) (allA_succ_of_accept 63 103 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 103 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 103 166 (accept_3_3 62 103 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 103 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 103 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 103 166
  (Polychromatic418967fa.accept_13_8_12_10_1_4414 60 103 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 103 166 (accept_3_3 59 103 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 103 166 (Polychromatic418967fa.accept_10_8_3_6_1_685 58 103 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 103 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 103 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 103 166 (accept_3_3 56 103 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 103 166
  (Polychromatic418967fa.accept_15_10_13_1_1_3698 55 103 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 103 166 (Polychromatic418967fa.accept_13_2_12_10_1_2649 54 103 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 103 166 (accept_3_3 53 103 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 103 166 (Polychromatic418967fa.accept_11_8_4_1_1_1000 52 103
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 103 166
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 103 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 103 166 (accept_3_3 50 103 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 103 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 103 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 103 166 (Polychromatic418967fa.accept_10_8_3_6_1_685 48 103 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 103 166 (accept_3_3 47 103 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 103 166 (Polychromatic418967fa.accept_13_7_12_10_1_640 46 103
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 103 166
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 103 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 103 166 (accept_3_3 44 103 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 103 166 (Polychromatic418967fa.accept_18_7_13_4_1_1670 43 103 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 103 166 (Polychromatic418967fa.accept_15_12_13_1_1_3695 42 103 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 103 166 (accept_3_3 41 103 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 103 166 (Polychromatic418967fa.accept_12_4_7_10_1_563 40 103
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 103 166
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 103 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 103 166 (accept_3_3 38 103 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 103 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 103 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 103 166 (Polychromatic418967fa.accept_17_2_1_13_1_6670 36 103 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 103 166 (accept_3_3 35 103 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 103 166 (Polychromatic418967fa.accept_13_8_12_10_1_4414 34 103
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 103 166
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 103 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 103 166 (accept_3_3 32 103 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 103 166 (Polychromatic418967fa.accept_14_3_5_12_1_4000 31 103 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 103 166 (Polychromatic418967fa.accept_11_8_4_1_1_1000 30 103 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 103 166 (accept_3_3 29 103 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 103 166 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 103
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 103 166
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 103 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 103 166 (accept_3_3 26 103 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 103 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 103 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 103 166 (Polychromatic418967fa.accept_13_11_12_10_1_2652 24 103 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 103 166 (accept_3_3 23 103 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 103 166 (Polychromatic418967fa.accept_13_9_12_10_1_242 22 103
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 103 166
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 103 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 103 166 (accept_3_3 20 103 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 103 166 (Polychromatic418967fa.accept_10_9_3_6_1_686 19 103 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 103 166 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 103 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 103 166 (accept_3_3 17 103 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 103 166 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 103
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 103 166
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 103 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 103 166 (accept_3_3 14 103 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 103 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 103 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 103 166 (Polychromatic418967fa.accept_15_12_13_1_1_3695 12 103 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 103 166 (accept_3_3 11 103 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 103 166 (Polychromatic418967fa.accept_14_10_5_12_1_3995 10 103
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 103 166
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 103 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 103 166 (accept_3_3 8 103 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  103 166 (Polychromatic418967fa.accept_10_7_3_6_1_644 7 103 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 103 166 (Polychromatic418967fa.accept_13_6_12_10_1_690 6 103 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 103 166 (accept_3_3 5 103 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 103 166 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 103 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 103 166
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 103 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 103 166 (accept_3_3 2 103 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  103 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 103 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 103 166)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 102 166
  (Eq.refl Bool.true) (allA_succ_of_gcd 64 102 166 2 32 51 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 102 166 (Polychromatic418967fa.accept_12_3_6_10_1_576 63 102
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 102 166 2 31 51 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 102 166
  (Polychromatic418967fa.accept_9_7_3_4_1_218 61 102 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 102 166 2 30 51 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 102 166 (accept_3_3 59 102 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 102 166 2 29 51 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 102 166 (Polychromatic418967fa.accept_7_1_4_5_1_35 57 102 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 102 166 2 28 51 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 102 166
  (Polychromatic418967fa.accept_7_6_4_5_1_314 55 102 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 102 166 2 27 51 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 102 166 (accept_3_3 53 102 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 102 166 2 26 51 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 102 166 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 102 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 102 166 2 25 51 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 102 166
  (Polychromatic418967fa.accept_15_4_12_1_1_1081 49 102 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 102 166 2 24 51 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 102 166 (accept_3_3 47 102 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 102 166 2 23 51 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 102 166 (Polychromatic418967fa.accept_12_9_6_10_1_1085 45 102 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 102 166 2 22 51 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 102 166
  (Polychromatic418967fa.accept_7_1_4_5_1_35 43 102 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 102 166 2 21 51 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 102 166 (accept_3_3 41 102 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 102 166 2 20 51 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 102 166 (Polychromatic418967fa.accept_12_3_6_10_1_576 39 102 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 102 166 2 19 51 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 102 166
  (Polychromatic418967fa.accept_7_2_4_5_1_313 37 102 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 166 2 18 51 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 102 166 (accept_3_3 35 102 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 102 166 2 17 51 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 102 166 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 102 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 102 166 2 16 51 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 102 166
  (Polychromatic418967fa.accept_10_1_2_6_1_638 31 102 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 166 2 15 51 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 102 166 (accept_3_3 29 102 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 102 166 2 14 51 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 102 166 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 102 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 102 166 2 13 51 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 102 166
  (Polychromatic418967fa.accept_9_7_3_4_1_218 25 102 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 166 2 12 51 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 102 166 (accept_3_3 23 102 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 102 166 2 11 51 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 102 166 (Polychromatic418967fa.accept_10_1_2_6_1_638 21 102 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 102 166 2 10 51 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 102 166
  (Polychromatic418967fa.accept_9_1_3_4_1_47 19 102 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 166 2 9 51 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 102 166 (accept_3_3 17 102 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  102 166 2 8 51 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 102 166 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 102 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 102 166 2 7 51 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 102 166 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 102 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 102 166 2 6 51 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 102 166 (accept_3_3 11 102 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 102 166 2 5 51 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 102 166
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 102 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 102 166 2 4 51 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 102 166 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 102 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102 166 2 3 51 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 102 166 (accept_3_3 5 102 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 102 166 2 2 51 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 102 166 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 102 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 102 166 2 1 51 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 166 (Polychromatic418967fa.accept_7_1_4_5_1_35 1
  102 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  166))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 101 166 (Eq.refl Bool.true)
  (allA_of_3_1 66 101 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 67 100 166 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 100 166 2 33 50 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 100 166 (accept_3_3 65 100 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 100 166 2 32 50 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 100 166 (Polychromatic418967fa.accept_14_7_2_12_1_1430 63 100 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 100 166 2 31 50 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 100 166
  (Polychromatic418967fa.accept_9_7_1_4_1_217 61 100 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 100 166 2 30 50 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 100 166 (accept_3_3 59 100 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 100 166 2 29 50 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 100 166 (Polychromatic418967fa.accept_9_3_1_4_1_216 57 100 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 100 166 2 28 50 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 100 166
  (Polychromatic418967fa.accept_12_7_4_10_1_572 55 100 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 100 166 2 27 50 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 100 166 (accept_3_3 53 100 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 100 166 2 26 50 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 100 166 (Polychromatic418967fa.accept_9_6_1_4_1_474 51 100 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 100 166 2 25 50 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 100 166
  (Polychromatic418967fa.accept_12_1_4_10_1_209 49 100 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 100 166 2 24 50 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 100 166 (accept_3_3 47 100 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 100 166 2 23 50 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 100 166 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 100 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 100 166 2 22 50 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 100 166
  (Polychromatic418967fa.accept_9_7_1_4_1_217 43 100 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 100 166 2 21 50 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 100 166 (accept_3_3 41 100 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 100 166 2 20 50 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 100 166 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 100 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 100 166 2 19 50 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 100 166
  (Polychromatic418967fa.accept_12_1_4_10_1_209 37 100 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 100 166 2 18 50 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 100 166 (accept_3_3 35 100 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 100 166 2 17 50 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 100 166 (Polychromatic418967fa.accept_9_6_1_4_1_474 33 100 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 100 166 2 16 50 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 100 166
  (Polychromatic418967fa.accept_7_3_2_5_1_147 31 100 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 100 166 2 15 50 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 100 166 (accept_3_3 29 100 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 100 166 2 14 50 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 100 166 (Polychromatic418967fa.accept_13_1_9_10_1_625 27 100 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 100 166 2 13 50 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 100 166
  (Polychromatic418967fa.accept_7_4_2_5_1_527 25 100 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 100 166 2 12 50 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 100 166 (accept_3_3 23 100 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 100 166 2 11 50 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 100 166 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 100 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 100 166 2 10 50 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 100 166
  (Polychromatic418967fa.accept_12_7_4_10_1_572 19 100 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 100 166 2 9 50 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 100 166 (accept_3_3 17 100 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  100 166 2 8 50 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 100 166 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 100 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 100 166 2 7 50 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 100 166 (Polychromatic418967fa.accept_12_1_4_10_1_209 13 100 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 100 166 2 6 50 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 100 166 (accept_3_3 11 100 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 100 166 2 5 50 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 100 166
  (Polychromatic418967fa.accept_15_9_10_1_1_1062 9 100 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 100 166 2 4 50 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 100 166 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 100 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 100 166 2 3 50 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 100 166 (accept_3_3 5 100 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 100 166 2 2 50 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 100 166 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 100 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 100 166 2 1 50 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 100 166 (Polychromatic418967fa.accept_12_1_4_10_1_209 1
  100 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 100
  166))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 99 166 (Eq.refl Bool.true)
  (allA_succ_of_accept 67 99 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 99 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 99 166 (Polychromatic418967fa.accept_7_3_1_5_1_44 66 99 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 99 166 (accept_3_3 65 99 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 166
  (Polychromatic418967fa.accept_13_12_8_10_1_1879 64 99 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 99 166 (Polychromatic418967fa.accept_10_3_9_6_1_94 63 99 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 99 166 (accept_3_3 62 99 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 99 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 99 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 99 166 (Polychromatic418967fa.accept_7_4_1_5_1_540 60
  99 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 99 166 (accept_3_3 59 99
  166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 166
  (Polychromatic418967fa.accept_22_14_11_12_1_7644 58 99 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 99 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 99 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 99 166 (accept_3_3 56 99 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 99 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 99 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 99 166
  (Polychromatic418967fa.accept_12_6_3_10_1_224 54 99 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 99 166 (accept_3_3 53 99 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  99 166 (Polychromatic418967fa.accept_7_3_1_5_1_44 52 99 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 99 166 (Polychromatic418967fa.accept_13_12_8_10_1_1879 51 99 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 99 166 (accept_3_3 50 99 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 99 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 99 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 99 166
  (Polychromatic418967fa.accept_7_6_1_5_1_322 48 99 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 99 166 (accept_3_3 47 99 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  99 166 (Polychromatic418967fa.accept_7_4_1_5_1_540 46 99 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 99 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 99 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 99 166 (accept_3_3 44 99 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 99 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 99 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 99 166
  (Polychromatic418967fa.accept_12_6_3_10_1_224 42 99 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 99 166 (accept_3_3 41 99 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  99 166 (Polychromatic418967fa.accept_15_10_9_1_1_3688 40 99 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 99 166 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 99 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 99 166 (accept_3_3 38 99 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 99 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 99 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 99 166
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 36 99 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 99 166 (accept_3_3 35 99 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  99 166 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 99 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 99 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 99 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 99 166 (accept_3_3 32 99 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 99 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 99 166
  (Polychromatic418967fa.accept_12_6_3_10_1_224 30 99 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 99 166 (accept_3_3 29 99 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  99 166 (Polychromatic418967fa.accept_13_2_8_10_1_1902 28 99 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 99 166 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 99 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 99 166 (accept_3_3 26 99 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 99 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 99 166
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 99 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 99 166 (accept_3_3 23 99 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  99 166 (Polychromatic418967fa.accept_15_7_9_1_1_473 22 99 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 99 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 99 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 99 166 (accept_3_3 20 99 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 99 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 99 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 99 166
  (Polychromatic418967fa.accept_7_4_1_5_1_540 18 99 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 99 166 (accept_3_3 17 99 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  99 166 (Polychromatic418967fa.accept_37_16_25_18_1_9209 16 99 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 99 166 (Polychromatic418967fa.accept_10_5_9_6_1_697 15 99 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 99 166 (accept_3_3 14 99 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 99 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 99 166
  (Polychromatic418967fa.accept_13_12_8_10_1_1879 12 99 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 99 166 (accept_3_3 11 99 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  99 166 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 99 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 99 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 99 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 166 (accept_3_3 8 99 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 99 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99 166
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 99 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 99 166 (accept_3_3 5 99 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99
  166 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 99 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 99 166 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 99 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 166 (accept_3_3 2 99 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 99 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 99 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  166)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 98 166 (Eq.refl Bool.true)
  (allA_of_3_1 69 98 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 70 97 166 (Eq.refl Bool.true)
  (allA_succ_of_accept 69 97 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 97 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 97 166 (accept_3_3 68 97 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 97 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 97 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 97 166 (Polychromatic418967fa.accept_9_3_7_4_1_53 66
  97 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 97 166 (accept_3_3 65 97
  166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 97 166 (Polychromatic418967fa.accept_7_1_6_5_1_39
  64 97 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 97 166
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 97 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 97 166 (accept_3_3 62 97 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  97 166 (Polychromatic418967fa.accept_10_1_7_6_1_91 61 97 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 97 166 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 97 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 97 166 (accept_3_3 59 97 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 97 166 (Polychromatic418967fa.accept_19_1_2_14_1_3666 58 97 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 97 166
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 97 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 97 166 (accept_3_3 56 97 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  97 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 97 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 97 166 (Polychromatic418967fa.accept_11_10_9_1_1_2186 54 97 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 97 166 (accept_3_3 53 97 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 97 166 (Polychromatic418967fa.accept_12_4_1_10_1_221 52 97 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 97 166
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 97 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 97 166 (accept_3_3 50 97 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  97 166 (Polychromatic418967fa.accept_18_13_7_4_1_2738 49 97 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 97 166 (Polychromatic418967fa.accept_9_3_7_4_1_53 48 97 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 97 166 (accept_3_3 47 97 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 97 166 (Polychromatic418967fa.accept_7_4_6_5_1_141 46 97 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 97 166
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 97 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 97 166 (accept_3_3 44 97 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  97 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 97 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 97 166 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 97 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 97 166 (accept_3_3 41 97 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 97 166 (Polychromatic418967fa.accept_12_4_1_10_1_221 40 97 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 97 166
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 97 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 97 166 (accept_3_3 38 97 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  97 166 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 97 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 97 166 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 97 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 97 166 (accept_3_3 35 97 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 97 166 (Polychromatic418967fa.accept_14_6_13_12_1_810 34 97 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 97 166
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 97 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 97 166 (accept_3_3 32 97 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  97 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 97 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 97 166 (Polychromatic418967fa.accept_9_3_7_4_1_53 30 97 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 97 166 (accept_3_3 29 97 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 97 166 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 97 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 97 166
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 97 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 97 166 (accept_3_3 26 97 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  97 166 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 97 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 97 166 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 97 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 97 166 (accept_3_3 23 97 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 97 166 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 97 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 97 166
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 97 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 97 166 (accept_3_3 20 97 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  97 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 97 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 97 166 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 97 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 97 166 (accept_3_3 17 97 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 97 166 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 97 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 97 166
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 97 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 97 166 (accept_3_3 14 97 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  97 166 (Polychromatic418967fa.accept_10_3_7_6_1_659 13 97 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 97 166 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 97 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 97 166 (accept_3_3 11 97 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 97 166 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 97 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 97 166
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 97 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 97 166 (accept_3_3 8 97 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 97
  166 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 97 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 97 166 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 97 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 97 166 (accept_3_3 5 97 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 97 166 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 97 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 97 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 97
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 166 (accept_3_3 2 97 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 97 166 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 97
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97
  166)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 96 166 (Eq.refl Bool.true)
  (allA_succ_of_gcd 70 96 166 2 35 48 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 96 166 (Polychromatic418967fa.accept_13_4_5_10_1_1247 69 96 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 96 166 2 34 48 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 96 166 (Polychromatic418967fa.accept_13_2_5_10_1_250
  67 96 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 96 166 2 33 48 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 96 166 (accept_3_3 65
  96 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 96 166 2 32 48 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 96 166
  (Polychromatic418967fa.accept_15_3_6_1_1_1834 63 96 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 96 166 2 31 48 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 96 166 (Polychromatic418967fa.accept_9_7_6_4_1_483 61 96 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 96 166 2 30 48 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 96 166 (accept_3_3 59 96 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 58 96 166 2 29 48 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 96 166 (Polychromatic418967fa.accept_9_3_6_4_1_210 57 96 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 96 166 2 28 48 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 96 166
  (Polychromatic418967fa.accept_9_1_6_4_1_49 55 96 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 96 166 2 27 48 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 96 166 (accept_3_3 53 96 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 96
  166 2 26 48 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  96 166 (Polychromatic418967fa.accept_18_15_6_4_1_5147 51 96 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 96 166 2 25 48 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 96 166 (Polychromatic418967fa.accept_17_15_11_13_1_2039 49 96 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 96 166 2 24 48 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 96 166 (accept_3_3 47 96 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 96 166 2 23 48 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 96 166
  (Polychromatic418967fa.accept_13_6_5_10_1_1213 45 96 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 96 166 2 22 48 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 96 166 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 96 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 96 166 2 21 48 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 96 166 (accept_3_3 41 96 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 96 166 2 20 48 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 96 166 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 96 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 96 166 2 19 48 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 96 166
  (Polychromatic418967fa.accept_9_1_6_4_1_49 37 96 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 96 166 2 18 48 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 96 166 (accept_3_3 35 96 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 96
  166 2 17 48 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  96 166 (Polychromatic418967fa.accept_15_3_6_1_1_1834 33 96 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 96 166 2 16 48 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 96 166 (Polychromatic418967fa.accept_20_11_16_6_1_6121 31 96 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 96 166 2 15 48 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 96 166 (accept_3_3 29 96 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 96 166 2 14 48 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 96 166
  (Polychromatic418967fa.accept_20_7_16_6_1_7784 27 96 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 96 166 2 13 48 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 96 166 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 96 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 96 166 2 12 48 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 96 166 (accept_3_3 23 96 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 96 166 2 11 48 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 96 166 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 96 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 96 166 2 10 48 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 96 166
  (Polychromatic418967fa.accept_9_1_6_4_1_49 19 96 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 96 166 2 9 48 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 96 166 (accept_3_3 17 96 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 96
  166 2 8 48 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  96 166 (Polychromatic418967fa.accept_11_4_8_1_1_1047 15 96 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 96 166 2 7 48 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 96 166 (Polychromatic418967fa.accept_19_13_1_14_1_3634 13 96 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96 166 2 6 48 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 96 166 (accept_3_3 11 96 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 96 166 2 5 48 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 96 166 (Polychromatic418967fa.accept_15_9_6_1_1_493 9 96 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 96 166 2 4 48 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 96 166
  (Polychromatic418967fa.accept_9_7_6_4_1_483 7 96 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 96 166 2 3 48 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 96 166 (accept_3_3 5 96 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 96 166
  2 2 48 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 96
  166 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 96 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 96 166 2 1 48 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 96 166 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 96 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 96
  166))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 95 166 (Eq.refl Bool.true)
  (allA_of_3_1 72 95 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 73 94 166 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 94 166 2 36 47 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 94 166 (accept_3_3 71 94 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 94
  166 2 35 47 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69
  94 166 (Polychromatic418967fa.accept_20_9_14_6_1_320 69 94 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 94 166 2 34 47 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 94 166 (Polychromatic418967fa.accept_13_2_3_10_1_658 67 94 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 94 166 2 33 47 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 94 166 (accept_3_3 65 94 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 94 166 2 32 47 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 94 166
  (Polychromatic418967fa.accept_13_11_3_10_1_4374 63 94 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 94 166 2 31 47 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 94 166 (Polychromatic418967fa.accept_14_5_10_12_1_1454 61 94 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 94 166 2 30 47 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 94 166 (accept_3_3 59 94 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 58 94 166 2 29 47 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 94 166 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 94 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 94 166 2 28 47 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 94 166
  (Polychromatic418967fa.accept_10_5_4_6_1_319 55 94 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 94 166 2 27 47 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 94 166 (accept_3_3 53 94 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 94
  166 2 26 47 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  94 166 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 94 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 94 166 2 25 47 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 94 166 (Polychromatic418967fa.accept_11_5_6_1_1_988 49 94 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 94 166 2 24 47 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 94 166 (accept_3_3 47 94 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 94 166 2 23 47 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 94 166
  (Polychromatic418967fa.accept_10_5_4_6_1_319 45 94 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 94 166 2 22 47 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 94 166 (Polychromatic418967fa.accept_7_1_3_5_1_33 43 94 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 94 166 2 21 47 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 94 166 (accept_3_3 41 94 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 94 166 2 20 47 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 94 166 (Polychromatic418967fa.accept_17_5_9_13_1_1093 39 94 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 94 166 2 19 47 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 94 166
  (Polychromatic418967fa.accept_7_2_3_5_1_34 37 94 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 94 166 2 18 47 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 94 166 (accept_3_3 35 94 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 94
  166 2 17 47 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  94 166 (Polychromatic418967fa.accept_13_7_3_10_1_656 33 94 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 94 166 2 16 47 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 94 166 (Polychromatic418967fa.accept_20_11_14_6_1_4714 31 94 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 94 166 2 15 47 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 94 166 (accept_3_3 29 94 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 94 166 2 14 47 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 94 166
  (Polychromatic418967fa.accept_11_5_6_1_1_988 27 94 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 94 166 2 13 47 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 94 166 (Polychromatic418967fa.accept_10_5_4_6_1_319 25 94 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 94 166 2 12 47 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 94 166 (accept_3_3 23 94 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 94 166 2 11 47 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 94 166 (Polychromatic418967fa.accept_17_4_9_13_1_2020 21 94 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 94 166 2 10 47 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 94 166
  (Polychromatic418967fa.accept_13_6_3_10_1_698 19 94 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 94 166 2 9 47 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 94 166 (accept_3_3 17 94 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 94
  166 2 8 47 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  94 166 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 94 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 94 166 2 7 47 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 94 166 (Polychromatic418967fa.accept_19_13_18_14_1_3522 13 94 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 94 166 2 6 47 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 94 166 (accept_3_3 11 94 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 94 166 2 5 47 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 94 166 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 94 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 94 166 2 4 47 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 94 166
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 7 94 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 94 166 2 3 47 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 94 166 (accept_3_3 5 94 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 94 166
  2 2 47 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 94
  166 (Polychromatic418967fa.accept_15_3_4_1_1_1072 3 94 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 94 166 2 1 47 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 94 166 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 94 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94
  166))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 93 166 (Eq.refl Bool.true)
  (allA_succ_of_accept 73 93 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 93 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 93 166 (Polychromatic418967fa.accept_11_6_5_1_1_586 72 93 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 93 166 (accept_3_3 71 93 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 166 (Polychromatic418967fa.accept_9_7_3_4_1_218 70
  93 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 166
  (Polychromatic418967fa.accept_9_6_3_4_1_477 69 93 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 93 166 (accept_3_3 68 93 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  93 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 93 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 93 166 (Polychromatic418967fa.accept_7_3_2_5_1_147 66 93 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 93 166 (accept_3_3 65 93 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 166 (Polychromatic418967fa.accept_9_1_3_4_1_47 64 93 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 166
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 93 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 93 166 (accept_3_3 62 93 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  93 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 93 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 93 166 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 93 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 93 166 (accept_3_3 59 93 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 166 (Polychromatic418967fa.accept_10_8_3_6_1_685 58 93 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 166
  (Polychromatic418967fa.accept_10_7_3_6_1_644 57 93 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 93 166 (accept_3_3 56 93 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  93 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 93 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 93 166 (Polychromatic418967fa.accept_12_6_9_10_1_565 54 93 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 93 166 (accept_3_3 53 93 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 166 (Polychromatic418967fa.accept_7_3_2_5_1_147 52 93 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 166
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 93 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 93 166 (accept_3_3 50 93 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  93 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 93 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 93 166 (Polychromatic418967fa.accept_10_8_3_6_1_685 48 93 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 93 166 (accept_3_3 47 93 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 166 (Polychromatic418967fa.accept_7_4_2_5_1_527 46 93 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 166
  (Polychromatic418967fa.accept_7_3_2_5_1_147 45 93 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 93 166 (accept_3_3 44 93 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  93 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 93 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 93 166 (Polychromatic418967fa.accept_9_6_3_4_1_477 42 93 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 93 166 (accept_3_3 41 93 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 166 (Polychromatic418967fa.accept_19_2_17_14_1_6399 40 93 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 166
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 93 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 93 166 (accept_3_3 38 93 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  93 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 93 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 93 166 (Polychromatic418967fa.accept_15_6_3_1_1_3678 36 93 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 93 166 (accept_3_3 35 93 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 166 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 93 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 166
  (Polychromatic418967fa.accept_9_6_3_4_1_477 33 93 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 93 166 (accept_3_3 32 93 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  93 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 93 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 93 166 (Polychromatic418967fa.accept_12_6_9_10_1_565 30 93 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 93 166 (accept_3_3 29 93 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 166 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 93 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 166
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 93 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 93 166 (accept_3_3 26 93 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  93 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 93 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 93 166 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 93 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 93 166 (accept_3_3 23 93 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 166 (Polychromatic418967fa.accept_17_5_8_13_1_7994 22 93 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 166
  (Polychromatic418967fa.accept_13_8_2_10_1_652 21 93 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 93 166 (accept_3_3 20 93 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  93 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 93 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 93 166 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 93 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 166 (accept_3_3 17 93 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 166 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 93 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 166
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 93 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 93 166 (accept_3_3 14 93 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  93 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 93 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 93 166 (Polychromatic418967fa.accept_13_12_2_10_1_2698 12 93 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 166 (accept_3_3 11 93 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 166 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 93 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 166
  (Polychromatic418967fa.accept_10_9_3_6_1_686 9 93 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 93 166 (accept_3_3 8 93 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93
  166 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 93 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 93 166 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 93 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 166 (accept_3_3 5 93 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 93 166 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 93 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 93
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 166 (accept_3_3 2 93 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 93
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  166)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 92 166 (Eq.refl
  Bool.true) (allA_of_3_1 75 92 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 76 91 166 (Eq.refl Bool.true)
  (allA_succ_of_accept 75 91 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 91 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 91 166 (accept_3_3 74 91 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 91 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 91 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 91 166 (Polychromatic418967fa.accept_10_2_1_6_1_634
  72 91 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 91 166 (accept_3_3 71
  91 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 91 166
  (Polychromatic418967fa.accept_9_7_1_4_1_217 70 91 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 91 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 91 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 91 166 (accept_3_3 68 91 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 91 166 (Polychromatic418967fa.accept_10_7_1_6_1_673 67 91 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 91 166 (Polychromatic418967fa.accept_9_3_1_4_1_216 66
  91 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 91 166 (accept_3_3 65 91
  166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 91 166
  (Polychromatic418967fa.accept_12_4_7_10_1_563 64 91 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 91 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 91 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 91 166 (accept_3_3 62 91 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 91 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 91 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 91 166 (Polychromatic418967fa.accept_9_6_1_4_1_474 60
  91 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 91 166 (accept_3_3 59 91
  166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 91 166
  (Polychromatic418967fa.accept_14_2_7_12_1_1485 58 91 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 91 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 91 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 91 166 (accept_3_3 56 91 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 91 166 (Polychromatic418967fa.accept_10_5_1_6_1_672 55 91 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 91 166
  (Polychromatic418967fa.accept_20_14_11_6_1_6264 54 91 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 91 166 (accept_3_3 53 91 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  91 166 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 91 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 91 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 91 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 91 166 (accept_3_3 50 91 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 91 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 91 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 91 166
  (Polychromatic418967fa.accept_9_3_1_4_1_216 48 91 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 91 166 (accept_3_3 47 91 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  91 166 (Polychromatic418967fa.accept_11_2_3_1_1_244 46 91 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 91 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 91 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 91 166 (accept_3_3 44 91 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 91 166 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 91 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 91 166
  (Polychromatic418967fa.accept_9_6_1_4_1_474 42 91 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 91 166 (accept_3_3 41 91 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  91 166 (Polychromatic418967fa.accept_12_4_7_10_1_563 40 91 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 91 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 91 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 91 166 (accept_3_3 38 91 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 91 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 91 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 91 166
  (Polychromatic418967fa.accept_16_4_11_6_1_5591 36 91 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 91 166 (accept_3_3 35 91 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  91 166 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 91 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 91 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 91 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 91 166 (accept_3_3 32 91 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 91 166 (Polychromatic418967fa.accept_21_10_7_19_1_9208 31 91 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 91 166
  (Polychromatic418967fa.accept_9_3_1_4_1_216 30 91 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 91 166 (accept_3_3 29 91 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  91 166 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 91 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 91 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 91 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 91 166 (accept_3_3 26 91 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 91 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 91 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 91 166
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 91 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 91 166 (accept_3_3 23 91 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  91 166 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 91 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 91 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 91 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 91 166 (accept_3_3 20 91 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 91 166 (Polychromatic418967fa.accept_14_5_7_12_1_4006 19 91 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 91 166
  (Polychromatic418967fa.accept_16_2_11_6_1_737 18 91 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 91 166 (accept_3_3 17 91 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  91 166 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 91 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 91 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 91 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 91 166 (accept_3_3 14 91 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 91 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 91 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 91 166
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 91 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 91 166 (accept_3_3 11 91 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  91 166 (Polychromatic418967fa.accept_19_10_15_14_1_5016 10 91 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 91 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 91 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 166 (accept_3_3 8 91 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 91 166 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 91 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 91 166
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 91 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 91 166 (accept_3_3 5 91 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91
  166 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 91 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 91 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 91 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 166 (accept_3_3 2 91 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 91 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 91 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91
  166)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 90 166 (Eq.refl
  Bool.true) (allA_succ_of_gcd 76 90 166 2 38 45 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 90 166 (Polychromatic418967fa.accept_12_3_6_10_1_576 75 90 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 90 166 2 37 45 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 90 166
  (Polychromatic418967fa.accept_13_8_12_10_1_4414 73 90 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 90 166 2 36 45 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 90 166 (accept_3_3 71 90 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 90
  166 2 35 45 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69
  90 166 (Polychromatic418967fa.accept_11_3_2_1_1_994 69 90 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 90 166 2 34 45 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 90 166 (Polychromatic418967fa.accept_7_4_6_5_1_141 67 90 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 90 166 2 33 45 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 90 166 (accept_3_3 65 90 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 90 166 2 32 45 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 90 166
  (Polychromatic418967fa.accept_12_3_6_10_1_576 63 90 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 90 166 2 31 45 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 90 166 (Polychromatic418967fa.accept_13_9_12_10_1_242 61 90 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 90 166 2 30 45 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 90 166 (accept_3_3 59 90 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 58 90 166 2 29 45 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 90 166 (Polychromatic418967fa.accept_7_1_6_5_1_39 57 90 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 90 166 2 28 45 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 90 166
  (Polychromatic418967fa.accept_14_13_6_12_1_3126 55 90 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 90 166 2 27 45 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 90 166 (accept_3_3 53 90 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 90
  166 2 26 45 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  90 166 (Polychromatic418967fa.accept_12_3_6_10_1_576 51 90 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 90 166 2 25 45 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 90 166 (Polychromatic418967fa.accept_17_15_5_13_1_6626 49 90 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 90 166 2 24 45 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 90 166 (accept_3_3 47 90 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 90 166 2 23 45 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 90 166
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 45 90 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 90 166 2 22 45 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 90 166 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 90 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 90 166 2 21 45 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 90 166 (accept_3_3 41 90 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 90 166 2 20 45 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 90 166 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 90 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 90 166 2 19 45 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 90 166
  (Polychromatic418967fa.accept_13_11_12_10_1_2652 37 90 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 90 166 2 18 45 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 90 166 (accept_3_3 35 90 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 90 166 2 17 45 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 90 166 (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 90 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 90 166 2 16 45 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 90 166 (Polychromatic418967fa.accept_25_6_15_16_1_9207
  31 90 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90 166 2 15 45 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 90 166 (accept_3_3 29
  90 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 90 166 2 14 45 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 90 166
  (Polychromatic418967fa.accept_12_3_6_10_1_576 27 90 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 90 166 2 13 45 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 90 166 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 90 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 90 166 2 12 45 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 166 (accept_3_3 23 90 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 90 166 2 11 45 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 90 166 (Polychromatic418967fa.accept_11_10_2_1_1_1036 21 90 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 90 166 2 10 45 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 90 166
  (Polychromatic418967fa.accept_13_6_12_10_1_690 19 90 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 90 166 2 9 45 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 90 166 (accept_3_3 17 90 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90
  166 2 8 45 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  90 166 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 90 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 90 166 2 7 45 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 90 166 (Polychromatic418967fa.accept_14_13_6_12_1_3126 13 90 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 166 2 6 45 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 166 (accept_3_3 11 90 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 90 166 2 5 45 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 90 166 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 90 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 90 166 2 4 45 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 90 166
  (Polychromatic418967fa.accept_13_7_12_10_1_640 7 90 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 90 166 2 3 45 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 90 166 (accept_3_3 5 90 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 90 166
  2 2 45 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 90
  166 (Polychromatic418967fa.accept_11_3_2_1_1_994 3 90 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 90 166 2 1 45 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 90 166 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 90 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 90
  166))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 78 89 166 (Eq.refl
  Bool.true) (allA_of_3_1 78 89 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 79 88 166 (Eq.refl Bool.true)
  (allA_succ_of_gcd 78 88 166 2 39 44 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 88 166 (accept_3_3 77 88 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 88
  166 2 38 44 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75
  88 166 (Polychromatic418967fa.accept_9_3_7_4_1_53 75 88 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 88 166 2 37 44 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 88 166 (Polychromatic418967fa.accept_9_1_7_4_1_52 73 88 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 88 166 2 36 44 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 88 166 (accept_3_3 71 88 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 88 166 2 35 44 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 88 166
  (Polychromatic418967fa.accept_7_6_4_5_1_314 69 88 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 88 166 2 34 44 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 88 166 (Polychromatic418967fa.accept_12_7_4_10_1_572 67 88 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 88 166 2 33 44 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 88 166 (accept_3_3 65 88 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 64 88 166 2 32 44 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 88 166 (Polychromatic418967fa.accept_10_3_8_6_1_326 63 88 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 88 166 2 31 44 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 88 166
  (Polychromatic418967fa.accept_12_1_4_10_1_209 61 88 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 88 166 2 30 44 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 88 166 (accept_3_3 59 88 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 88
  166 2 29 44 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57
  88 166 (Polychromatic418967fa.accept_7_1_4_5_1_35 57 88 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 88 166 2 28 44 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 88 166 (Polychromatic418967fa.accept_7_6_4_5_1_314 55 88 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 88 166 2 27 44 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 88 166 (accept_3_3 53 88 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 88 166 2 26 44 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 88 166
  (Polychromatic418967fa.accept_7_2_4_5_1_313 51 88 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 88 166 2 25 44 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 88 166 (Polychromatic418967fa.accept_12_1_4_10_1_209 49 88 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 88 166 2 24 44 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 88 166 (accept_3_3 47 88 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 88 166 2 23 44 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 88 166 (Polychromatic418967fa.accept_19_7_12_14_1_9206 45 88
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 88 166 2 22 44 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 88 166
  (Polychromatic418967fa.accept_7_1_4_5_1_35 43 88 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 88 166 2 21 44 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 88 166 (accept_3_3 41 88 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 88
  166 2 20 44 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  88 166 (Polychromatic418967fa.accept_9_3_7_4_1_53 39 88 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 88 166 2 19 44 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 88 166 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 88 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 88 166 2 18 44 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 88 166 (accept_3_3 35 88 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 88 166 2 17 44 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 88 166
  (Polychromatic418967fa.accept_9_6_7_4_1_212 33 88 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 88 166 2 16 44 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 88 166 (Polychromatic418967fa.accept_12_7_4_10_1_572 31 88 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 88 166 2 15 44 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 88 166 (accept_3_3 29 88 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 88 166 2 14 44 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 88 166 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 88 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 88 166 2 13 44 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 88 166
  (Polychromatic418967fa.accept_12_1_4_10_1_209 25 88 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 88 166 2 12 44 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 88 166 (accept_3_3 23 88 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 88
  166 2 11 44 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  88 166 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 88 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 88 166 2 10 44 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 88 166 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 88 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 88 166 2 9 44 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 88 166 (accept_3_3 17 88 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 88 166 2 8 44 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 88 166 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 88 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 88 166 2 7 44 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 88 166
  (Polychromatic418967fa.accept_7_6_4_5_1_314 13 88 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 88 166 2 6 44 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 88 166 (accept_3_3 11 88 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 88
  166 2 5 44 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  88 166 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 88 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 88 166 2 4 44 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 88 166 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 88 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 88 166 2 3 44 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 88 166 (accept_3_3 5 88 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 88 166 2 2 44 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 88 166 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 88 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 88 166 2 1 44 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 88 166
  (Polychromatic418967fa.accept_7_1_4_5_1_35 1 88 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 88 166))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 87 166
  (Eq.refl Bool.true) (allA_succ_of_accept 79 87 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 87 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 87 166
  (Polychromatic418967fa.accept_7_1_3_5_1_33 78 87 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 87 166 (accept_3_3 77 87 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  87 166 (Polychromatic418967fa.accept_20_16_7_6_1_7815 76 87 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 87 166 (Polychromatic418967fa.accept_9_3_6_4_1_210 75 87 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 87 166 (accept_3_3 74 87 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 87 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 87 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 87 166
  (Polychromatic418967fa.accept_7_2_3_5_1_34 72 87 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 87 166 (accept_3_3 71 87 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  87 166 (Polychromatic418967fa.accept_9_7_6_4_1_483 70 87 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 87 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 87 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 87 166 (accept_3_3 68 87 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 87 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 87 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 87 166
  (Polychromatic418967fa.accept_9_3_6_4_1_210 66 87 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 87 166 (accept_3_3 65 87 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  87 166 (Polychromatic418967fa.accept_7_1_3_5_1_33 64 87 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 87 166 (Polychromatic418967fa.accept_10_3_7_6_1_659 63 87 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 87 166 (accept_3_3 62 87 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 87 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 87 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 87 166
  (Polychromatic418967fa.accept_18_6_15_4_1_3916 60 87 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 87 166 (accept_3_3 59 87 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  87 166 (Polychromatic418967fa.accept_7_2_3_5_1_34 58 87 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 87 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 87 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 87 166 (accept_3_3 56 87 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 87 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 87 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 87 166
  (Polychromatic418967fa.accept_12_6_3_10_1_224 54 87 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 87 166 (accept_3_3 53 87 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  87 166 (Polychromatic418967fa.accept_9_7_6_4_1_483 52 87 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 87 166 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 87 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 87 166 (accept_3_3 50 87 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 87 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 87 166
  (Polychromatic418967fa.accept_9_3_6_4_1_210 48 87 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 87 166 (accept_3_3 47 87 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  87 166 (Polychromatic418967fa.accept_9_1_6_4_1_49 46 87 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 87 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 87 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 87 166 (accept_3_3 44 87 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 87 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 87 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 87 166
  (Polychromatic418967fa.accept_11_9_10_1_1_581 42 87 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 87 166 (accept_3_3 41 87 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  87 166 (Polychromatic418967fa.accept_13_1_9_10_1_625 40 87 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 87 166 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 87 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 87 166 (accept_3_3 38 87 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 87 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 87 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 87 166
  (Polychromatic418967fa.accept_7_1_3_5_1_33 36 87 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 87 166 (accept_3_3 35 87 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  87 166 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 87 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 87 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 87 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 87 166 (accept_3_3 32 87 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 87 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 87 166
  (Polychromatic418967fa.accept_7_2_3_5_1_34 30 87 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 87 166 (accept_3_3 29 87 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  87 166 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 87 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 87 166 (Polychromatic418967fa.accept_13_1_9_10_1_625 27 87 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 87 166 (accept_3_3 26 87 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 87 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 87 166
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 24 87 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 87 166 (accept_3_3 23 87 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  87 166 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 87 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 87 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 87 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 87 166 (accept_3_3 20 87 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 87 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 87 166
  (Polychromatic418967fa.accept_12_6_3_10_1_224 18 87 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 87 166 (accept_3_3 17 87 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  87 166 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 87 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 87 166 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 87 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 166 (accept_3_3 14 87 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 87 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 87 166
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 87 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 87 166 (accept_3_3 11 87 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  87 166 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 87 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 87 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 87 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 166 (accept_3_3 8 87 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 87 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87 166
  (Polychromatic418967fa.accept_12_6_3_10_1_224 6 87 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 87 166 (accept_3_3 5 87 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87
  166 (Polychromatic418967fa.accept_15_4_12_1_1_1081 4 87 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 87 166 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 87 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 166 (accept_3_3 2 87 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 87 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  166)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 81 86 166 (Eq.refl
  Bool.true) (allA_of_3_1 81 86 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 82 85 166 (Eq.refl Bool.true)
  (allA_succ_of_accept 81 85 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 85 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 85 166 (accept_3_3 80 85 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 85 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 85 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 85 166
  (Polychromatic418967fa.accept_21_15_1_19_1_9205 78 85 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 85 166 (accept_3_3 77 85 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  85 166 (Polychromatic418967fa.accept_7_6_1_5_1_322 76 85 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 85 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 85 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 85 166 (accept_3_3 74 85 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 85 166 (Polychromatic418967fa.accept_7_3_1_5_1_44 73 85 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 85 166
  (Polychromatic418967fa.accept_20_12_5_6_1_6205 72 85 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 85 166 (accept_3_3 71 85 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  85 166 (Polychromatic418967fa.accept_11_4_8_1_1_1047 70 85 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 85 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 85 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 85 166 (accept_3_3 68 85 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 85 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 85 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 85 166
  (Polychromatic418967fa.accept_7_3_1_5_1_44 66 85 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 85 166 (accept_3_3 65 85 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  85 166 (Polychromatic418967fa.accept_10_4_5_6_1_651 64 85 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 85 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 85 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 85 166 (accept_3_3 62 85 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 85 166 (Polychromatic418967fa.accept_10_1_5_6_1_649 61 85 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 85 166
  (Polychromatic418967fa.accept_7_4_1_5_1_540 60 85 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 85 166 (accept_3_3 59 85 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  85 166 (Polychromatic418967fa.accept_15_13_10_1_1_1862 58 85 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 85 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 85 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 85 166 (accept_3_3 56 85 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 85 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 85 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 85 166
  (Polychromatic418967fa.accept_10_4_5_6_1_651 54 85 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 85 166 (accept_3_3 53 85 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  85 166 (Polychromatic418967fa.accept_7_3_1_5_1_44 52 85 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 85 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 85 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 85 166 (accept_3_3 50 85 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 85 166 (Polychromatic418967fa.accept_10_9_5_6_1_691 49 85 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 85 166
  (Polychromatic418967fa.accept_7_6_1_5_1_322 48 85 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 85 166 (accept_3_3 47 85 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  85 166 (Polychromatic418967fa.accept_7_4_1_5_1_540 46 85 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 85 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 85 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 85 166 (accept_3_3 44 85 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 85 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 85 166
  (Polychromatic418967fa.accept_13_3_7_10_1_668 42 85 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 85 166 (accept_3_3 41 85 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  85 166 (Polychromatic418967fa.accept_12_4_1_10_1_221 40 85 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 85 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 85 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 85 166 (accept_3_3 38 85 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 85 166 (Polychromatic418967fa.accept_11_4_8_1_1_1047 37 85 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 166
  (Polychromatic418967fa.accept_15_6_10_1_1_3675 36 85 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 85 166 (accept_3_3 35 85 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  85 166 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 85 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 85 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 85 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 166 (accept_3_3 32 85 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 85 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 85 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 85 166
  (Polychromatic418967fa.accept_13_4_7_10_1_1200 30 85 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 85 166 (accept_3_3 29 85 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  85 166 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 85 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 85 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 85 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 166 (accept_3_3 26 85 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 85 166 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 85 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 85 166
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 85 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 85 166 (accept_3_3 23 85 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  85 166 (Polychromatic418967fa.accept_15_7_10_1_1_1836 22 85 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 85 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 85 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 85 166 (accept_3_3 20 85 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 85 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 85 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 166
  (Polychromatic418967fa.accept_7_4_1_5_1_540 18 85 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 85 166 (accept_3_3 17 85 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  85 166 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 85 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 85 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 85 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 85 166 (accept_3_3 14 85 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 166 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 85 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 166
  (Polychromatic418967fa.accept_13_12_7_10_1_2662 12 85 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 166 (accept_3_3 11 85 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  85 166 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 85 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 85 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 85 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 166 (accept_3_3 8 85 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 85 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 166
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 85 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 85 166 (accept_3_3 5 85 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85
  166 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 85 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 85 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 85 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 166 (accept_3_3 2 85 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 85 166 (Polychromatic418967fa.accept_10_1_5_6_1_649 1 85 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  166)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 84 166 (Eq.refl
  Bool.true) (allA_succ_of_gcd 82 84 166 2 41 42 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 84 166 (Polychromatic418967fa.accept_13_3_6_10_1_2658 81 84 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 84 166 2 40 42 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 84 166
  (Polychromatic418967fa.accept_9_7_3_4_1_218 79 84 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 84 166 2 39 42 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 84 166 (accept_3_3 77 84 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 84
  166 2 38 42 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75
  84 166 (Polychromatic418967fa.accept_10_5_4_6_1_319 75 84 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 84 166 2 37 42 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 84 166 (Polychromatic418967fa.accept_9_1_3_4_1_47 73 84 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 84 166 2 36 42 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 84 166 (accept_3_3 71 84 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 84 166 2 35 42 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 84 166
  (Polychromatic418967fa.accept_9_6_3_4_1_477 69 84 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 84 166 2 34 42 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 84 166 (Polychromatic418967fa.accept_13_2_6_10_1_2703 67 84 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 84 166 2 33 42 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 84 166 (accept_3_3 65 84 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 64 84 166 2 32 42 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 84 166 (Polychromatic418967fa.accept_17_12_16_13_1_7951 63 84
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 84 166 2 31 42 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 84 166
  (Polychromatic418967fa.accept_9_7_3_4_1_218 61 84 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 84 166 2 30 42 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 84 166 (accept_3_3 59 84 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 84
  166 2 29 42 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57
  84 166 (Polychromatic418967fa.accept_13_5_6_10_1_2659 57 84 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 84 166 2 28 42 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 84 166 (Polychromatic418967fa.accept_9_1_3_4_1_47 55 84 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 84 166 2 27 42 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 84 166 (accept_3_3 53 84 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 84 166 2 26 42 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 84 166
  (Polychromatic418967fa.accept_9_6_3_4_1_477 51 84 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 84 166 2 25 42 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 84 166 (Polychromatic418967fa.accept_22_5_18_12_1_7664 49 84 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 84 166 2 24 42 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 84 166 (accept_3_3 47 84 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 84 166 2 23 42 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 84 166 (Polychromatic418967fa.accept_10_5_4_6_1_319 45 84 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 84 166 2 22 42 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 84 166
  (Polychromatic418967fa.accept_9_7_3_4_1_218 43 84 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 84 166 2 21 42 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 84 166 (accept_3_3 41 84 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 84
  166 2 20 42 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  84 166 (Polychromatic418967fa.accept_11_6_7_1_1_564 39 84 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 84 166 2 19 42 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 84 166 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 84 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 84 166 2 18 42 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 84 166 (accept_3_3 35 84 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 84 166 2 17 42 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 84 166
  (Polychromatic418967fa.accept_9_6_3_4_1_477 33 84 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 84 166 2 16 42 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 84 166 (Polychromatic418967fa.accept_13_5_6_10_1_2659 31 84 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84 166 2 15 42 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 84 166 (accept_3_3 29 84 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 84 166 2 14 42 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 84 166 (Polychromatic418967fa.accept_16_11_4_6_1_4422 27 84 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 84 166 2 13 42 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 84 166
  (Polychromatic418967fa.accept_9_7_3_4_1_218 25 84 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 84 166 2 12 42 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 84 166 (accept_3_3 23 84 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 84
  166 2 11 42 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  84 166 (Polychromatic418967fa.accept_15_6_9_1_1_1823 21 84 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 84 166 2 10 42 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 84 166 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 84 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84 166 2 9 42 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 84 166 (accept_3_3 17 84 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 84 166 2 8 42 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 84 166 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 84 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 84 166 2 7 42 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 166
  (Polychromatic418967fa.accept_16_13_4_6_1_2322 13 84 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 84 166 2 6 42 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 84 166 (accept_3_3 11 84 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84
  166 2 5 42 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  84 166 (Polychromatic418967fa.accept_13_9_6_10_1_666 9 84 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 84 166 2 4 42 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 84 166 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 84 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 166 2 3 42 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 166 (accept_3_3 5 84 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 84 166 2 2 42 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 84 166 (Polychromatic418967fa.accept_13_3_6_10_1_2658 3 84 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 84 166 2 1 42 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 166
  (Polychromatic418967fa.accept_9_1_3_4_1_47 1 84 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 84 166))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 166
  (allA_of_3_1 83 83 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 82 166 (allA_succ_of_accept 81 82 166
  (Polychromatic418967fa.accept_10_1_2_6_1_638 81 82 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 82 166 2 40 41 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 79 82 166 (Polychromatic418967fa.accept_9_7_1_4_1_217 79 82 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 82 166 2 39 41 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 82 166 (accept_3_3 77 82 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 76 82 166 2 38 41 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 82 166 (Polychromatic418967fa.accept_9_3_1_4_1_216 75 82 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 82 166 2 37 41 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 82 166
  (Polychromatic418967fa.accept_13_8_4_10_1_4358 73 82 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 82 166 2 36 41 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 82 166 (accept_3_3 71 82 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 82
  166 2 35 41 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69
  82 166 (Polychromatic418967fa.accept_9_6_1_4_1_474 69 82 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 82 166 2 34 41 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 82 166 (Polychromatic418967fa.accept_16_3_2_6_1_4461 67 82 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 82 166 2 33 41 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 82 166 (accept_3_3 65 82 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 82 166 2 32 41 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 82 166
  (Polychromatic418967fa.accept_13_11_4_10_1_3440 63 82 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 82 166 2 31 41 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 82 166 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 82 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 82 166 2 30 41 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 82 166 (accept_3_3 59 82 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 58 82 166 2 29 41 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 82 166 (Polychromatic418967fa.accept_9_3_1_4_1_216 57 82 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 82 166 2 28 41 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 82 166
  (Polychromatic418967fa.accept_15_10_7_1_1_3686 55 82 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 82 166 2 27 41 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 82 166 (accept_3_3 53 82 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 82
  166 2 26 41 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  82 166 (Polychromatic418967fa.accept_9_6_1_4_1_474 51 82 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 82 166 2 25 41 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 82 166 (Polychromatic418967fa.accept_16_1_2_6_1_2295 49 82 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 82 166 2 24 41 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 82 166 (accept_3_3 47 82 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 82 166 2 23 41 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 82 166
  (Polychromatic418967fa.accept_13_6_4_10_1_660 45 82 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 82 166 2 22 41 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 82 166 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 82 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 82 166 2 21 41 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 82 166 (accept_3_3 41 82 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 82 166 2 20 41 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 82 166 (Polychromatic418967fa.accept_9_3_1_4_1_216 39 82 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 82 166 2 19 41 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 82 166
  (Polychromatic418967fa.accept_13_11_4_10_1_3440 37 82 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 82 166 2 18 41 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 82 166 (accept_3_3 35 82 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 82
  166 2 17 41 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  82 166 (Polychromatic418967fa.accept_9_6_1_4_1_474 33 82 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 82 166 2 16 41 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 82 166 (Polychromatic418967fa.accept_10_1_2_6_1_638 31 82 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 82 166 2 15 41 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 82 166 (accept_3_3 29 82 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 82 166 2 14 41 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 82 166
  (Polychromatic418967fa.accept_13_1_4_10_1_622 27 82 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 82 166 2 13 41 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 82 166 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 82 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 82 166 2 12 41 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 82 166 (accept_3_3 23 82 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 82 166 2 11 41 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 82 166 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 82 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 82 166 2 10 41 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 82 166
  (Polychromatic418967fa.accept_13_6_4_10_1_660 19 82 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 82 166 2 9 41 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 82 166 (accept_3_3 17 82 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 82
  166 2 8 41 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  82 166 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 82 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 82 166 2 7 41 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 82 166 (Polychromatic418967fa.accept_18_13_10_4_1_5150 13 82 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 82 166 2 6 41 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 82 166 (accept_3_3 11 82 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 82 166 2 5 41 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 82 166 (Polychromatic418967fa.accept_15_9_7_1_1_1075 9 82 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 82 166 2 4 41 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 82 166
  (Polychromatic418967fa.accept_9_7_1_4_1_217 7 82 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 82 166 2 3 41 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 82 166 (accept_3_3 5 82 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 82 166
  2 2 41 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 82
  166 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 82 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 82 166 2 1 41 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 82 166 (Polychromatic418967fa.accept_10_1_2_6_1_638 1 82 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 82
  166)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 81 166
  (allA_succ_of_accept 80 81 166 (accept_3_3 80 81 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  81 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 81 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 166 (Polychromatic418967fa.accept_7_1_4_5_1_35 78 81 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 166 (accept_3_3 77 81 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 166 (Polychromatic418967fa.accept_7_6_4_5_1_314 76 81 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 166
  (Polychromatic418967fa.accept_4_3_1_2_1_62 75 81 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 81 166 (accept_3_3 74 81 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  81 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 81 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 81 166 (Polychromatic418967fa.accept_7_2_4_5_1_313 72 81 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 166 (accept_3_3 71 81 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 166 (Polychromatic418967fa.accept_15_10_6_1_1_3707 70 81 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 166
  (Polychromatic418967fa.accept_7_6_4_5_1_314 69 81 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 81 166 (accept_3_3 68 81 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  81 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 81 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 81 166 (Polychromatic418967fa.accept_12_6_9_10_1_565 66 81 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 166 (accept_3_3 65 81 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 166 (Polychromatic418967fa.accept_7_1_4_5_1_35 64 81 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 166
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 81 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 81 166 (accept_3_3 62 81 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  81 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 81 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 81 166 (Polychromatic418967fa.accept_19_3_5_14_1_3584 60 81 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 166 (accept_3_3 59 81 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 166 (Polychromatic418967fa.accept_7_2_4_5_1_313 58 81 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 166
  (Polychromatic418967fa.accept_7_1_4_5_1_35 57 81 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 81 166 (accept_3_3 56 81 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  81 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 81 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 81 166 (Polychromatic418967fa.accept_12_6_9_10_1_565 54 81 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 166 (accept_3_3 53 81 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 166 (Polychromatic418967fa.accept_10_2_1_6_1_634 52 81 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 166
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 81 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 81 166 (accept_3_3 50 81 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  81 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 81 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 81 166 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 81 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 166 (accept_3_3 47 81 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 166 (Polychromatic418967fa.accept_13_7_3_10_1_656 46 81 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 166
  (Polychromatic418967fa.accept_10_5_1_6_1_672 45 81 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 81 166 (accept_3_3 44 81 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  81 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 81 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 81 166 (Polychromatic418967fa.accept_10_2_1_6_1_634 42 81 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 166 (accept_3_3 41 81 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 166 (Polychromatic418967fa.accept_15_10_6_1_1_3707 40 81 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 166
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 81 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 81 166 (accept_3_3 38 81 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  81 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 81 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 81 166 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 81 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 166 (accept_3_3 35 81 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 166 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 81 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 166
  (Polychromatic418967fa.accept_13_7_3_10_1_656 33 81 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 81 166 (accept_3_3 32 81 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  81 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 81 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 81 166 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 81 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 166 (accept_3_3 29 81 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 166 (Polychromatic418967fa.accept_13_2_3_10_1_658 28 81 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 166
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 81 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 81 166 (accept_3_3 26 81 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  81 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 81 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 81 166 (Polychromatic418967fa.accept_13_11_3_10_1_4374 24 81 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 166 (accept_3_3 23 81 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 166 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 81 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 166
  (Polychromatic418967fa.accept_16_5_1_6_1_3367 21 81 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 81 166 (accept_3_3 20 81 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  81 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 81 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 81 166 (Polychromatic418967fa.accept_12_6_9_10_1_565 18 81 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 166 (accept_3_3 17 81 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 166 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 81 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 166
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 81 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 81 166 (accept_3_3 14 81 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  81 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 81 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 81 166 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 81 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 166 (accept_3_3 11 81 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 166 (Polychromatic418967fa.accept_15_10_6_1_1_3707 10 81 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 166
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 81 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 81 166 (accept_3_3 8 81 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81
  166 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 81 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 81 166 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 81 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 166 (accept_3_3 5 81 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 81 166 (Polychromatic418967fa.accept_21_4_18_19_1_9189 4 81 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 81
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 166 (accept_3_3 2 81 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 81
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81
  166))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 166 (allA_of_3_1 80
  80 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 79 166 (allA_succ_of_accept 78 79 166
  (Polychromatic418967fa.accept_9_6_7_4_1_212 78 79 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 79 166 (accept_3_3 77 79 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  79 166 (Polychromatic418967fa.accept_11_10_2_1_1_1036 76 79 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 79 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 79 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 79 166 (accept_3_3 74 79 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 79 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 79 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 79 166
  (Polychromatic418967fa.accept_15_12_4_1_1_3746 72 79 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 79 166 (accept_3_3 71 79 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  79 166 (Polychromatic418967fa.accept_18_16_7_4_1_3901 70 79 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 79 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 79 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 79 166 (accept_3_3 68 79 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 79 166 (Polychromatic418967fa.accept_7_4_2_5_1_527 67 79 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 79 166
  (Polychromatic418967fa.accept_7_3_2_5_1_147 66 79 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 79 166 (accept_3_3 65 79 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  79 166 (Polychromatic418967fa.accept_9_1_7_4_1_52 64 79 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 79 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 79 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 79 166 (accept_3_3 62 79 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 79 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 79 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 79 166
  (Polychromatic418967fa.accept_7_4_2_5_1_527 60 79 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 79 166 (accept_3_3 59 79 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  79 166 (Polychromatic418967fa.accept_11_3_2_1_1_994 58 79 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 79 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 79 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 79 166 (accept_3_3 56 79 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 79 166 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 79 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 79 166
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 54 79 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 79 166 (accept_3_3 53 79 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  79 166 (Polychromatic418967fa.accept_7_3_2_5_1_147 52 79 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 79 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 79 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 79 166 (accept_3_3 50 79 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 79 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 79 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 79 166
  (Polychromatic418967fa.accept_9_3_7_4_1_53 48 79 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 79 166 (accept_3_3 47 79 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  79 166 (Polychromatic418967fa.accept_7_4_2_5_1_527 46 79 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 79 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 79 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 79 166 (accept_3_3 44 79 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 79 166 (Polychromatic418967fa.accept_10_3_9_6_1_94 43 79 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 79 166
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 79 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 79 166 (accept_3_3 41 79 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  79 166 (Polychromatic418967fa.accept_12_4_7_10_1_563 40 79 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 79 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 79 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 79 166 (accept_3_3 38 79 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 79 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 79 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 79 166
  (Polychromatic418967fa.accept_11_3_2_1_1_994 36 79 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 79 166 (accept_3_3 35 79 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  79 166 (Polychromatic418967fa.accept_18_16_7_4_1_3901 34 79 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 79 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 79 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 79 166 (accept_3_3 32 79 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 79 166 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 79 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 79 166
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 79 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 79 166 (accept_3_3 29 79 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  79 166 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 79 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 79 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 79 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 166 (accept_3_3 26 79 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 79 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 79 166
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 79 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 79 166 (accept_3_3 23 79 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  79 166 (Polychromatic418967fa.accept_13_9_1_10_1_647 22 79 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 79 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 79 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 166 (accept_3_3 20 79 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 166 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 79 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 166
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 79 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 79 166 (accept_3_3 17 79 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  79 166 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 79 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 79 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 79 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 166 (accept_3_3 14 79 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 79 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 166
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 79 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 166 (accept_3_3 11 79 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  79 166 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 79 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 79 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 79 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 166 (accept_3_3 8 79 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 166 (Polychromatic418967fa.accept_14_7_9_12_1_3975 7 79 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 166
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 79 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 166 (accept_3_3 5 79 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  166 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 79 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 79 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 79 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 166 (accept_3_3 2 79 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 79 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 79 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79
  166))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 78 166
  (allA_succ_of_accept 77 78 166 (accept_3_3 77 78 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 78
  166 2 38 39 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75
  78 166 (Polychromatic418967fa.accept_9_3_6_4_1_210 75 78 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 78 166 2 37 39 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 78 166 (Polychromatic418967fa.accept_7_3_1_5_1_44 73 78 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 166 2 36 39 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 166 (accept_3_3 71 78 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 78 166 2 35 39 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 78 166
  (Polychromatic418967fa.accept_7_6_1_5_1_322 69 78 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 78 166 2 34 39 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 78 166 (Polychromatic418967fa.accept_7_4_1_5_1_540 67 78 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78 166 2 33 39 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 78 166 (accept_3_3 65 78 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 64 78 166 2 32 39 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 78 166 (Polychromatic418967fa.accept_10_3_8_6_1_326 63 78 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 78 166 2 31 39 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 78 166
  (Polychromatic418967fa.accept_9_7_6_4_1_483 61 78 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 78 166 2 30 39 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 78 166 (accept_3_3 59 78 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 78
  166 2 29 39 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57
  78 166 (Polychromatic418967fa.accept_9_3_6_4_1_210 57 78 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 78 166 2 28 39 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 78 166 (Polychromatic418967fa.accept_7_6_1_5_1_322 55 78 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 78 166 2 27 39 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 78 166 (accept_3_3 53 78 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 78 166 2 26 39 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 78 166
  (Polychromatic418967fa.accept_12_3_6_10_1_576 51 78 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 78 166 2 25 39 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 78 166 (Polychromatic418967fa.accept_15_4_3_1_1_487 49 78 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 78 166 2 24 39 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 78 166 (accept_3_3 47 78 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 78 166 2 23 39 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 78 166 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 78 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 78 166 2 22 39 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 78 166
  (Polychromatic418967fa.accept_9_7_6_4_1_483 43 78 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 78 166 2 21 39 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 78 166 (accept_3_3 41 78 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 78
  166 2 20 39 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  78 166 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 78 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 78 166 2 19 39 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 78 166 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 78 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78 166 2 18 39 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 78 166 (accept_3_3 35 78 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 78 166 2 17 39 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 78 166
  (Polychromatic418967fa.accept_10_3_8_6_1_326 33 78 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 78 166 2 16 39 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 78 166 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 78 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 78 166 2 15 39 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 78 166 (accept_3_3 29 78 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 78 166 2 14 39 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 78 166 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 78 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 78 166 2 13 39 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 78 166
  (Polychromatic418967fa.accept_7_4_1_5_1_540 25 78 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 78 166 2 12 39 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 78 166 (accept_3_3 23 78 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 78
  166 2 11 39 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  78 166 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 78 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 78 166 2 10 39 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 78 166 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 78 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 166 2 9 39 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 166 (accept_3_3 17 78 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78 166 2 8 39 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 78 166 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 78 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 78 166 2 7 39 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 78 166
  (Polychromatic418967fa.accept_7_6_1_5_1_322 13 78 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 78 166 2 6 39 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 78 166 (accept_3_3 11 78 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 78
  166 2 5 39 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  78 166 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 78 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 78 166 2 4 39 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 78 166 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 78 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 166 2 3 39 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 166 (accept_3_3 5 78 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 166 2 2 39 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 78 166 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 78 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 78 166 2 1 39 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 166
  (Polychromatic418967fa.accept_9_1_6_4_1_49 1 78 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 78 166)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 166
  (allA_of_3_1 77 77 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 76 166 (allA_succ_of_accept 75 76 166
  (Polychromatic418967fa.accept_11_9_10_1_1_581 75 76 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 76 166 2 37 38 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 73 76 166 (Polychromatic418967fa.accept_12_1_4_10_1_209 73 76 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 76 166 2 36 38 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 76 166 (accept_3_3 71 76 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 70 76 166 2 35 38 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 76 166 (Polychromatic418967fa.accept_13_4_11_10_1_1226 69 76
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 76 166 2 34 38 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 76 166
  (Polychromatic418967fa.accept_7_4_6_5_1_141 67 76 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 76 166 2 33 38 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 76 166 (accept_3_3 65 76 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 76
  166 2 32 38 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63
  76 166 (Polychromatic418967fa.accept_25_13_1_16_1_9204 63 76 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 76 166 2 31 38 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 76 166 (Polychromatic418967fa.accept_12_1_4_10_1_209 61 76 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 76 166 2 30 38 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 76 166 (accept_3_3 59 76 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 76 166 2 29 38 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 76 166
  (Polychromatic418967fa.accept_7_1_6_5_1_39 57 76 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 76 166 2 28 38 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 76 166 (Polychromatic418967fa.accept_12_7_4_10_1_572 55 76 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 76 166 2 27 38 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 76 166 (accept_3_3 53 76 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 76 166 2 26 38 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 76 166 (Polychromatic418967fa.accept_13_12_11_10_1_2711 51 76
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 76 166 2 25 38 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 76 166
  (Polychromatic418967fa.accept_12_1_4_10_1_209 49 76 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 76 166 2 24 38 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 76 166 (accept_3_3 47 76 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 76
  166 2 23 38 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  76 166 (Polychromatic418967fa.accept_27_18_22_4_1_9203 45 76 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 76 166 2 22 38 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 76 166 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 76 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 76 166 2 21 38 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 76 166 (accept_3_3 41 76 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 76 166 2 20 38 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 76 166
  (Polychromatic418967fa.accept_7_4_6_5_1_141 39 76 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 76 166 2 19 38 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 76 166 (Polychromatic418967fa.accept_12_1_4_10_1_209 37 76 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 76 166 2 18 38 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 76 166 (accept_3_3 35 76 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 76 166 2 17 38 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 76 166 (Polychromatic418967fa.accept_22_11_10_12_1_9202 33 76
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 76 166 2 16 38 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 76 166
  (Polychromatic418967fa.accept_11_9_10_1_1_581 31 76 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 76 166 2 15 38 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 76 166 (accept_3_3 29 76 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 76
  166 2 14 38 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  76 166 (Polychromatic418967fa.accept_13_1_11_10_1_1258 27 76 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 76 166 2 13 38 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 76 166 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 76 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 76 166 2 12 38 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 76 166 (accept_3_3 23 76 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 76 166 2 11 38 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 76 166
  (Polychromatic418967fa.accept_13_8_11_10_1_636 21 76 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 76 166 2 10 38 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 76 166 (Polychromatic418967fa.accept_12_7_4_10_1_572 19 76 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 76 166 2 9 38 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 76 166 (accept_3_3 17 76 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 76 166 2 8 38 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 76 166 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 76 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 76 166 2 7 38 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 76 166 (Polychromatic418967fa.accept_11_2_10_1_1_1017
  13 76 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 76 166 2 6 38 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 76 166 (accept_3_3 11
  76 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 76 166 2 5 38 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 76 166
  (Polychromatic418967fa.accept_11_9_10_1_1_581 9 76 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 76 166 2 4 38 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 76 166 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 76 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 76 166 2 3 38 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 76 166 (accept_3_3 5 76 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 76 166 2 2 38 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 76 166 (Polychromatic418967fa.accept_13_3_11_10_1_2647 3 76 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 76 166 2 1 38 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 76 166 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 76
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76
  166)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 166 (allA_succ_of_accept
  74 75 166 (accept_3_3 74 75 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 75 166
  (Polychromatic418967fa.accept_4_1_3_2_1_3 73 75 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 75 166 (Polychromatic418967fa.accept_19_15_18_14_1_3564 72 75 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 75 166 (accept_3_3 71 75 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 75 166 (Polychromatic418967fa.accept_9_7_3_4_1_218 70 75 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 69
  75 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 166 (accept_3_3 68 75
  166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 166 (Polychromatic418967fa.accept_6_1_3_4_1_1
  67 75 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 75 166
  (Polychromatic418967fa.accept_12_6_3_10_1_224 66 75 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 75 166 (accept_3_3 65 75 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  75 166 (Polychromatic418967fa.accept_9_1_3_4_1_47 64 75 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 75 166 (Polychromatic418967fa.accept_14_7_5_12_1_1439 63 75 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 166 (accept_3_3 62 75 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 75 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 75 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 75 166
  (Polychromatic418967fa.accept_9_6_3_4_1_477 60 75 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 75 166 (accept_3_3 59 75 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  75 166 (Polychromatic418967fa.accept_19_1_18_14_1_6392 58 75 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 75 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 75 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 166 (accept_3_3 56 75 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 75 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 75 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 75 166
  (Polychromatic418967fa.accept_10_4_5_6_1_651 54 75 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 75 166 (accept_3_3 53 75 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  75 166 (Polychromatic418967fa.accept_9_7_3_4_1_218 52 75 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 75 166 (Polychromatic418967fa.accept_9_6_3_4_1_477 51 75 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 166 (accept_3_3 50 75 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 75 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 75 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 75 166
  (Polychromatic418967fa.accept_19_10_18_14_1_7867 48 75 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 75 166 (accept_3_3 47 75 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 75 166 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 75 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 75 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 166 (accept_3_3 44 75 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 43
  75 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 75 166
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 75 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 75 166 (accept_3_3 41 75 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  75 166 (Polychromatic418967fa.accept_17_6_7_13_1_3062 40 75 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 75 166 (Polychromatic418967fa.accept_10_9_5_6_1_691 39 75 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 166 (accept_3_3 38 75 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 75 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 75 166
  (Polychromatic418967fa.accept_16_4_11_6_1_5591 36 75 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 75 166 (accept_3_3 35 75 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  75 166 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 75 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 75 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 75 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 166 (accept_3_3 32 75 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 75 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 75 166
  (Polychromatic418967fa.accept_12_6_3_10_1_224 30 75 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 75 166 (accept_3_3 29 75 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  75 166 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 75 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 75 166 (Polychromatic418967fa.accept_21_6_12_19_1_6032 27 75 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 166 (accept_3_3 26 75 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 75 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 75 166
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 75 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 75 166 (accept_3_3 23 75 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  75 166 (Polychromatic418967fa.accept_19_3_18_14_1_5020 22 75 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 75 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 75 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 166 (accept_3_3 20 75 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 75 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 166
  (Polychromatic418967fa.accept_12_6_3_10_1_224 18 75 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 75 166 (accept_3_3 17 75 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  75 166 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 75 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 75 166 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 75 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 166 (accept_3_3 14 75 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 75 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 75 166
  (Polychromatic418967fa.accept_20_12_15_6_1_9201 12 75 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 75 166 (accept_3_3 11 75 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  75 166 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 75 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 75 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 75 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 166 (accept_3_3 8 75 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 75 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 166
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 75 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 166 (accept_3_3 5 75 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75
  166 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 75 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 75 166 (Polychromatic418967fa.accept_14_3_5_12_1_4000 3 75 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 166 (accept_3_3 2 75 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 75 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 75 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  166))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 166 (allA_of_3_1 74 74
  166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 73 166 (allA_succ_of_accept 72 73 166
  (Polychromatic418967fa.accept_7_2_3_5_1_34 72 73 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 73 166 (accept_3_3 71 73 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  73 166 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 73 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 73 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 73 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 166 (accept_3_3 68 73 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 73 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 166
  (Polychromatic418967fa.accept_9_3_1_4_1_216 66 73 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 73 166 (accept_3_3 65 73 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  73 166 (Polychromatic418967fa.accept_7_1_3_5_1_33 64 73 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 73 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 73 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 166 (accept_3_3 62 73 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 166 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 73 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 166
  (Polychromatic418967fa.accept_9_6_1_4_1_474 60 73 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 166 (accept_3_3 59 73 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 166 (Polychromatic418967fa.accept_7_2_3_5_1_34 58 73 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 73 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 166 (accept_3_3 56 73 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 73 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 166
  (Polychromatic418967fa.accept_13_2_8_10_1_1902 54 73 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 166 (accept_3_3 53 73 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 166 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 73 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 73 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 166 (accept_3_3 50 73 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 166 (Polychromatic418967fa.accept_10_9_3_6_1_686 49 73 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 166
  (Polychromatic418967fa.accept_9_3_1_4_1_216 48 73 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 166 (accept_3_3 47 73 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 166 (Polychromatic418967fa.accept_13_7_8_10_1_2663 46 73 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 73 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 166 (accept_3_3 44 73 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 73 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 166
  (Polychromatic418967fa.accept_9_6_1_4_1_474 42 73 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 166 (accept_3_3 41 73 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 166 (Polychromatic418967fa.accept_12_4_1_10_1_221 40 73 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 73 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 166 (accept_3_3 38 73 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 166 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 73 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 166
  (Polychromatic418967fa.accept_7_1_3_5_1_33 36 73 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 166 (accept_3_3 35 73 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 166 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 73 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 73 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 166 (accept_3_3 32 73 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 73 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 166
  (Polychromatic418967fa.accept_7_2_3_5_1_34 30 73 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 166 (accept_3_3 29 73 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 166 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 73 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 73 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 166 (accept_3_3 26 73 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 166 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 73 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 166
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 73 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 166 (accept_3_3 23 73 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 166 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 73 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 73 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 166 (accept_3_3 20 73 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 73 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 166
  (Polychromatic418967fa.accept_10_8_3_6_1_685 18 73 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 166 (accept_3_3 17 73 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 166 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 73 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 73 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 166 (accept_3_3 14 73 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 166 (Polychromatic418967fa.accept_16_13_9_6_1_2306 13 73 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 166
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 73 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 166 (accept_3_3 11 73 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 166 (Polychromatic418967fa.accept_15_10_13_1_1_3698 10 73 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 73 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 166 (accept_3_3 8 73 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 73 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 166
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 73 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 166 (accept_3_3 5 73 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  166 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 73 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 73 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 73 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 166 (accept_3_3 2 73 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 73 166 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 73 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  166))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 166 (allA_succ_of_accept 71
  72 166 (accept_3_3 71 72 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 72 166 2 35 36 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 72 166
  (Polychromatic418967fa.accept_13_4_7_10_1_1200 69 72 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 72 166 2 34 36 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 72 166 (Polychromatic418967fa.accept_7_4_2_5_1_527 67 72 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 166 2 33 36 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 166 (accept_3_3 65 72 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 64 72 166 2 32 36 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 72 166 (Polychromatic418967fa.accept_14_7_2_12_1_1430 63 72 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 72 166 2 31 36 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 72 166
  (Polychromatic418967fa.accept_10_1_2_6_1_638 61 72 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 72 166 2 30 36 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 72 166 (accept_3_3 59 72 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 72
  166 2 29 36 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57
  72 166 (Polychromatic418967fa.accept_20_17_12_6_1_6171 57 72 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 72 166 2 28 36 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 72 166 (Polychromatic418967fa.accept_13_3_7_10_1_668 55 72 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 72 166 2 27 36 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 72 166 (accept_3_3 53 72 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 72 166 2 26 36 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 72 166
  (Polychromatic418967fa.accept_10_1_2_6_1_638 51 72 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 72 166 2 25 36 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 72 166 (Polychromatic418967fa.accept_11_5_6_1_1_988 49 72 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 166 2 24 36 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 166 (accept_3_3 47 72 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 72 166 2 23 36 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 72 166 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 72 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 72 166 2 22 36 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 72 166
  (Polychromatic418967fa.accept_13_4_7_10_1_1200 43 72 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 72 166 2 21 36 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 72 166 (accept_3_3 41 72 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 72
  166 2 20 36 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  72 166 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 72 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 72 166 2 19 36 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 72 166 (Polychromatic418967fa.accept_17_3_4_13_1_2030 37 72 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 72 166 2 18 36 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 72 166 (accept_3_3 35 72 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 72 166 2 17 36 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 72 166
  (Polychromatic418967fa.accept_21_12_9_19_1_9200 33 72 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 72 166 2 16 36 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 72 166 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 72 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 166 2 15 36 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 166 (accept_3_3 29 72 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 72 166 2 14 36 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 72 166 (Polychromatic418967fa.accept_11_5_6_1_1_988 27 72 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 72 166 2 13 36 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 166
  (Polychromatic418967fa.accept_7_4_2_5_1_527 25 72 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 72 166 2 12 36 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 72 166 (accept_3_3 23 72 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72
  166 2 11 36 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  72 166 (Polychromatic418967fa.accept_10_1_2_6_1_638 21 72 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 72 166 2 10 36 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 72 166 (Polychromatic418967fa.accept_15_4_12_1_1_1081 19 72 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72 166 2 9 36 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 72 166 (accept_3_3 17 72 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 72 166 2 8 36 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 72 166 (Polychromatic418967fa.accept_20_15_12_6_1_9199 15 72
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 72 166 2 7 36 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 166
  (Polychromatic418967fa.accept_15_13_12_1_1_1841 13 72 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 72 166 2 6 36 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 72 166 (accept_3_3 11 72 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72
  166 2 5 36 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  72 166 (Polychromatic418967fa.accept_17_9_4_13_1_3057 9 72 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 72 166 2 4 36 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 72 166 (Polychromatic418967fa.accept_11_7_6_1_1_2182 7 72 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 166 2 3 36 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 166 (accept_3_3 5 72 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 72 166 2 2 36 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 72 166 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 72 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 72 166 2 1 36 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 166
  (Polychromatic418967fa.accept_10_1_2_6_1_638 1 72 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 72 166)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 166
  (allA_of_3_1 71 71 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 70 166 (allA_succ_of_accept 69 70 166
  (Polychromatic418967fa.accept_9_6_7_4_1_212 69 70 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 70 166 2 34 35 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 70 166 (Polychromatic418967fa.accept_13_2_5_10_1_250 67 70 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 70 166 2 33 35 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 70 166 (accept_3_3 65 70 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 64 70 166 2 32 35 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 70 166 (Polychromatic418967fa.accept_11_8_4_1_1_1000 63 70 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 70 166 2 31 35 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 70 166
  (Polychromatic418967fa.accept_18_7_16_4_1_1674 61 70 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 70 166 2 30 35 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 70 166 (accept_3_3 59 70 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 70
  166 2 29 35 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57
  70 166 (Polychromatic418967fa.accept_9_3_7_4_1_53 57 70 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 70 166 2 28 35 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 70 166 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 70 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 70 166 2 27 35 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 70 166 (accept_3_3 53 70 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 70 166 2 26 35 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 70 166
  (Polychromatic418967fa.accept_9_6_7_4_1_212 51 70 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 70 166 2 25 35 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 70 166 (Polychromatic418967fa.accept_17_15_2_13_1_4153 49 70 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 70 166 2 24 35 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 70 166 (accept_3_3 47 70 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 70 166 2 23 35 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 70 166 (Polychromatic418967fa.accept_13_6_5_10_1_1213 45 70 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 70 166 2 22 35 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 70 166
  (Polychromatic418967fa.accept_13_4_5_10_1_1247 43 70 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 70 166 2 21 35 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 70 166 (accept_3_3 41 70 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 70
  166 2 20 35 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  70 166 (Polychromatic418967fa.accept_9_3_7_4_1_53 39 70 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 70 166 2 19 35 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 70 166 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 70 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 70 166 2 18 35 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 70 166 (accept_3_3 35 70 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 70 166 2 17 35 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 70 166
  (Polychromatic418967fa.accept_9_6_7_4_1_212 33 70 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 70 166 2 16 35 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 70 166 (Polychromatic418967fa.accept_19_12_13_14_1_9198 31 70 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 70 166 2 15 35 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 70 166 (accept_3_3 29 70 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 70 166 2 14 35 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 70 166 (Polychromatic418967fa.accept_19_8_13_14_1_2373 27 70
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 70 166 2 13 35 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 70 166
  (Polychromatic418967fa.accept_18_7_16_4_1_1674 25 70 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 70 166 2 12 35 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 70 166 (accept_3_3 23 70 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 70
  166 2 11 35 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  70 166 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 70 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 70 166 2 10 35 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 70 166 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 70 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 70 166 2 9 35 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 70 166 (accept_3_3 17 70 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 70 166 2 8 35 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 70 166 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 70 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 70 166 2 7 35 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 70 166
  (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 70 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 70 166 2 6 35 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 70 166 (accept_3_3 11 70 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70
  166 2 5 35 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  70 166 (Polychromatic418967fa.accept_15_9_10_1_1_1062 9 70 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 70 166 2 4 35 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 70 166 (Polychromatic418967fa.accept_15_7_10_1_1_1836 7 70 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 70 166 2 3 35 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 70 166 (accept_3_3 5 70 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 70 166 2 2 35 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 70 166 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 70 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 70 166 2 1 35 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 70 166
  (Polychromatic418967fa.accept_9_1_7_4_1_52 1 70 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 70 166)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 166
  (allA_succ_of_accept 68 69 166 (accept_3_3 68 69 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  69 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 69 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 69 166 (Polychromatic418967fa.accept_9_3_6_4_1_210 66 69 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 69 166 (accept_3_3 65 69 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 166 (Polychromatic418967fa.accept_7_1_6_5_1_39 64 69 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 166
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 69 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 69 166 (accept_3_3 62 69 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  69 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 69 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 69 166 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 69 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 69 166 (accept_3_3 59 69 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 166 (Polychromatic418967fa.accept_13_6_4_10_1_660 58 69 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 166
  (Polychromatic418967fa.accept_7_1_6_5_1_39 57 69 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 69 166 (accept_3_3 56 69 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  69 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 69 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 69 166 (Polychromatic418967fa.accept_12_6_9_10_1_565 54 69 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 69 166 (accept_3_3 53 69 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 166 (Polychromatic418967fa.accept_9_7_6_4_1_483 52 69 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 166
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 69 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 69 166 (accept_3_3 50 69 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  69 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 69 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 69 166 (Polychromatic418967fa.accept_9_3_6_4_1_210 48 69 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 69 166 (accept_3_3 47 69 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 166 (Polychromatic418967fa.accept_7_4_6_5_1_141 46 69 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 166
  (Polychromatic418967fa.accept_10_5_9_6_1_697 45 69 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 69 166 (accept_3_3 44 69 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  69 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 69 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 69 166 (Polychromatic418967fa.accept_12_6_9_10_1_565 42 69 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 69 166 (accept_3_3 41 69 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 166 (Polychromatic418967fa.accept_13_1_4_10_1_622 40 69 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 166
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 69 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 69 166 (accept_3_3 38 69 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  69 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 69 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 69 166 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 69 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 69 166 (accept_3_3 35 69 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 166 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 69 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 166
  (Polychromatic418967fa.accept_10_3_9_6_1_94 33 69 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 69 166 (accept_3_3 32 69 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  69 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 69 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 69 166 (Polychromatic418967fa.accept_9_3_6_4_1_210 30 69 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 166 (accept_3_3 29 69 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 166 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 69 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 166
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 69 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 69 166 (accept_3_3 26 69 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  69 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 69 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 69 166 (Polychromatic418967fa.accept_11_2_3_1_1_244 24 69 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 166 (accept_3_3 23 69 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 166 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 69 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 166
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 69 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 69 166 (accept_3_3 20 69 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  69 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 69 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 69 166 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 69 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 166 (accept_3_3 17 69 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 166 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 69 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 166
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 69 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 69 166 (accept_3_3 14 69 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  69 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 69 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 69 166 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 69 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 166 (accept_3_3 11 69 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 166 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 69 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 166
  (Polychromatic418967fa.accept_18_9_15_4_1_5173 9 69 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 69 166 (accept_3_3 8 69 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69
  166 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 69 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 69 166 (Polychromatic418967fa.accept_12_6_9_10_1_565 6 69 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 166 (accept_3_3 5 69 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 69 166 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 69 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 69
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 166 (accept_3_3 2 69 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 69
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  166))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 166 (allA_of_3_1 68 68 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 67 166 (allA_succ_of_accept 66 67 166
  (Polychromatic418967fa.accept_15_6_7_1_1_93 66 67 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 166 (accept_3_3 65 67 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 166 (Polychromatic418967fa.accept_7_1_4_5_1_35 64 67 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 67 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 166 (accept_3_3 62 67 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 67 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 166
  (Polychromatic418967fa.accept_13_8_2_10_1_652 60 67 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 166 (accept_3_3 59 67 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 166 (Polychromatic418967fa.accept_7_2_4_5_1_313 58 67 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 67 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 166 (accept_3_3 56 67 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 166 (Polychromatic418967fa.accept_7_6_4_5_1_314 55 67 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 166
  (Polychromatic418967fa.accept_15_9_7_1_1_1075 54 67 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 166 (accept_3_3 53 67 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 166 (Polychromatic418967fa.accept_12_4_7_10_1_563 52 67 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 67 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 166 (accept_3_3 50 67 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 67 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 166
  (Polychromatic418967fa.accept_7_6_4_5_1_314 48 67 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 166 (accept_3_3 47 67 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 166 (Polychromatic418967fa.accept_17_12_16_13_1_7951 46 67 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 67 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 166 (accept_3_3 44 67 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 166 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 67 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 166
  (Polychromatic418967fa.accept_13_3_2_10_1_2697 42 67 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 166 (accept_3_3 41 67 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 166 (Polychromatic418967fa.accept_12_4_7_10_1_563 40 67 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 67 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 166 (accept_3_3 38 67 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 67 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 166
  (Polychromatic418967fa.accept_7_1_4_5_1_35 36 67 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 166 (accept_3_3 35 67 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 166 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 67 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 67 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 166 (accept_3_3 32 67 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 166 (Polychromatic418967fa.accept_10_1_7_6_1_91 31 67 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 166
  (Polychromatic418967fa.accept_7_2_4_5_1_313 30 67 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 166 (accept_3_3 29 67 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 166 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 67 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 67 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 166 (accept_3_3 26 67 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 67 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 166
  (Polychromatic418967fa.accept_13_11_2_10_1_4399 24 67 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 166 (accept_3_3 23 67 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 166 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 67 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 67 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 166 (accept_3_3 20 67 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 166 (Polychromatic418967fa.accept_13_6_2_10_1_1240 19 67 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 166
  (Polychromatic418967fa.accept_13_5_2_10_1_248 18 67 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 166 (accept_3_3 17 67 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 166 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 67 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 67 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 166 (accept_3_3 14 67 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 67 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 166
  (Polychromatic418967fa.accept_13_12_2_10_1_2698 12 67 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 166 (accept_3_3 11 67 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 166 (Polychromatic418967fa.accept_15_10_7_1_1_3686 10 67 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 67 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 166 (accept_3_3 8 67 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 166 (Polychromatic418967fa.accept_18_7_13_4_1_1670 7 67 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 166
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 67 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 166 (accept_3_3 5 67 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  166 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 67 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 67 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 67 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 166 (accept_3_3 2 67 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 67 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  166))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 166 (allA_succ_of_accept 65 66
  166 (accept_3_3 65 66 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 66 166 2 32 33 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 66 166
  (Polychromatic418967fa.accept_12_3_6_10_1_576 63 66 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 66 166 2 31 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 66 166 (Polychromatic418967fa.accept_9_7_3_4_1_218 61 66 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 166 2 30 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 166 (accept_3_3 59 66 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 58 66 166 2 29 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 66 166 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 66 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 66 166 2 28 33 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 66 166
  (Polychromatic418967fa.accept_9_1_3_4_1_47 55 66 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 66 166 2 27 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 66 166 (accept_3_3 53 66 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 66
  166 2 26 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  66 166 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 66 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 66 166 2 25 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 66 166 (Polychromatic418967fa.accept_16_1_2_6_1_2295 49 66 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 166 2 24 33 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 166 (accept_3_3 47 66 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 66 166 2 23 33 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 66 166
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 45 66 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 66 166 2 22 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 66 166 (Polychromatic418967fa.accept_7_1_3_5_1_33 43 66 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 66 166 2 21 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 66 166 (accept_3_3 41 66 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 66 166 2 20 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 66 166 (Polychromatic418967fa.accept_12_3_6_10_1_576 39 66 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 66 166 2 19 33 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 66 166
  (Polychromatic418967fa.accept_7_2_3_5_1_34 37 66 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 66 166 2 18 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 66 166 (accept_3_3 35 66 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 66
  166 2 17 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  66 166 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 66 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 66 166 2 16 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 66 166 (Polychromatic418967fa.accept_19_12_9_14_1_6365 31 66 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 166 2 15 33 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 166 (accept_3_3 29 66 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 66 166 2 14 33 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 66 166
  (Polychromatic418967fa.accept_12_3_6_10_1_576 27 66 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 66 166 2 13 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 66 166 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 66 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 166 2 12 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 166 (accept_3_3 23 66 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 166 2 11 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 66 166 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 66 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 66 166 2 10 33 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 66 166
  (Polychromatic418967fa.accept_9_1_3_4_1_47 19 66 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 66 166 2 9 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 66 166 (accept_3_3 17 66 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66
  166 2 8 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  66 166 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 66 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 66 166 2 7 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 66 166 (Polychromatic418967fa.accept_23_13_20_5_1_9197 13 66 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 166 2 6 33 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 166 (accept_3_3 11 66 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 66 166 2 5 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 66 166 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 66 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 66 166 2 4 33 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 66 166
  (Polychromatic418967fa.accept_9_7_3_4_1_218 7 66 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 66 166 2 3 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 66 166 (accept_3_3 5 66 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 166
  2 2 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 66
  166 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 66 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 66 166 2 1 33 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 66 166 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 66 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  166)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 166 (allA_of_3_1 65 65 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 64 166 (allA_succ_of_accept 63 64 166
  (Polychromatic418967fa.accept_13_11_12_10_1_2652 63 64 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 64 166 2 31 32 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 64 166 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 64 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 64 166 2 30 32 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 64 166 (accept_3_3 59 64 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 64 166 2 29 32 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 64 166
  (Polychromatic418967fa.accept_9_3_1_4_1_216 57 64 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 64 166 2 28 32 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 64 166 (Polychromatic418967fa.accept_7_6_1_5_1_322 55 64 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 64 166 2 27 32 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 64 166 (accept_3_3 53 64 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 64 166 2 26 32 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 64 166 (Polychromatic418967fa.accept_9_6_1_4_1_474 51 64 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 64 166 2 25 32 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 64 166
  (Polychromatic418967fa.accept_12_1_4_10_1_209 49 64 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 64 166 2 24 32 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 64 166 (accept_3_3 47 64 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 64
  166 2 23 32 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  64 166 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 64 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 64 166 2 22 32 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 64 166 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 64 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 64 166 2 21 32 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 64 166 (accept_3_3 41 64 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 64 166 2 20 32 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 64 166
  (Polychromatic418967fa.accept_7_4_1_5_1_540 39 64 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 64 166 2 19 32 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 64 166 (Polychromatic418967fa.accept_12_1_4_10_1_209 37 64 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 64 166 2 18 32 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 64 166 (accept_3_3 35 64 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 64 166 2 17 32 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 64 166 (Polychromatic418967fa.accept_9_6_1_4_1_474 33 64 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 64 166 2 16 32 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 64 166
  (Polychromatic418967fa.accept_7_3_1_5_1_44 31 64 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 64 166 2 15 32 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 64 166 (accept_3_3 29 64 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 64
  166 2 14 32 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  64 166 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 64 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 64 166 2 13 32 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 64 166 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 64 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 64 166 2 12 32 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 64 166 (accept_3_3 23 64 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 64 166 2 11 32 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 64 166
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 64 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 64 166 2 10 32 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 64 166 (Polychromatic418967fa.accept_12_7_4_10_1_572 19 64 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 64 166 2 9 32 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 64 166 (accept_3_3 17 64 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 64 166 2 8 32 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 64 166 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 64 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 64 166 2 7 32 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 64 166 (Polychromatic418967fa.accept_7_6_1_5_1_322 13
  64 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 64 166 2 6 32 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 64 166 (accept_3_3 11
  64 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 64 166 2 5 32 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 64 166
  (Polychromatic418967fa.accept_13_9_12_10_1_242 9 64 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 64 166 2 4 32 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 64 166 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 64 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 64 166 2 3 32 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 64 166 (accept_3_3 5 64 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 64 166 2 2 32 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 64 166 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 64 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 64 166 2 1 32 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 64 166 (Polychromatic418967fa.accept_12_1_4_10_1_209 1
  64 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64
  166)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 166 (allA_succ_of_accept 62 63 166
  (accept_3_3 62 63 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 63 166
  (Polychromatic418967fa.accept_4_1_3_2_1_3 61 63 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 63 166 (Polychromatic418967fa.accept_13_8_11_10_1_636 60 63 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 63 166 (accept_3_3 59 63 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 63 166 (Polychromatic418967fa.accept_10_8_3_6_1_685 58 63 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 57
  63 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 166 (accept_3_3 56 63
  166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 63 166 (Polychromatic418967fa.accept_6_1_3_4_1_1
  55 63 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 63 166
  (Polychromatic418967fa.accept_12_6_3_10_1_224 54 63 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 63 166 (accept_3_3 53 63 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  63 166 (Polychromatic418967fa.accept_17_1_12_13_1_448 52 63 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 63 166 (Polychromatic418967fa.accept_13_12_11_10_1_2711 51 63 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 166 (accept_3_3 50 63 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 63 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 63 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 63 166
  (Polychromatic418967fa.accept_10_8_3_6_1_685 48 63 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 63 166 (accept_3_3 47 63 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  63 166 (Polychromatic418967fa.accept_19_8_6_14_1_5009 46 63 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 63 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 63 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 166 (accept_3_3 44 63 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 63 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 63 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 63 166
  (Polychromatic418967fa.accept_12_6_3_10_1_224 42 63 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 63 166 (accept_3_3 41 63 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  63 166 (Polychromatic418967fa.accept_13_1_11_10_1_1258 40 63 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 63 166 (Polychromatic418967fa.accept_10_9_3_6_1_686 39 63 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 166 (accept_3_3 38 63 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 63 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 63 166
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 36 63 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 63 166 (accept_3_3 35 63 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  63 166 (Polychromatic418967fa.accept_13_8_11_10_1_636 34 63 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 63 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 63 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 166 (accept_3_3 32 63 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 63 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 63 166
  (Polychromatic418967fa.accept_12_6_3_10_1_224 30 63 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 63 166 (accept_3_3 29 63 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  63 166 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 63 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 63 166 (Polychromatic418967fa.accept_10_7_3_6_1_644 27 63 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 166 (accept_3_3 26 63 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 63 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 63 166
  (Polychromatic418967fa.accept_19_5_6_14_1_5010 24 63 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 63 166 (accept_3_3 23 63 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  63 166 (Polychromatic418967fa.accept_23_22_17_5_1_9196 22 63 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 63 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 63 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 166 (accept_3_3 20 63 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 63 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 63 166
  (Polychromatic418967fa.accept_10_8_3_6_1_685 18 63 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 63 166 (accept_3_3 17 63 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  63 166 (Polychromatic418967fa.accept_13_3_11_10_1_2647 16 63 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 63 166 (Polychromatic418967fa.accept_11_4_8_1_1_1047 15 63 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 166 (accept_3_3 14 63 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 63 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 63 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 63 166
  (Polychromatic418967fa.accept_13_12_11_10_1_2711 12 63 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 63 166 (accept_3_3 11 63 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 63 166 (Polychromatic418967fa.accept_19_10_6_14_1_4959 10 63 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 63 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 166 (accept_3_3 8 63 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 63
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63 166
  (Polychromatic418967fa.accept_12_6_3_10_1_224 6 63 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 166 (accept_3_3 5 63 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63
  166 (Polychromatic418967fa.accept_11_4_8_1_1_1047 4 63 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 63 166 (Polychromatic418967fa.accept_13_3_11_10_1_2647 3 63 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 166 (accept_3_3 2 63 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 63 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  166))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 166 (allA_of_3_1 62 62 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 61 166 (allA_succ_of_accept 60 61 166
  (Polychromatic418967fa.accept_9_6_7_4_1_212 60 61 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 166 (accept_3_3 59 61 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 166 (Polychromatic418967fa.accept_13_6_9_10_1_1201 58 61 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 61 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 166 (accept_3_3 56 61 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 61 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 166
  (Polychromatic418967fa.accept_17_3_10_13_1_2021 54 61 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 166 (accept_3_3 53 61 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 166 (Polychromatic418967fa.accept_10_2_1_6_1_634 52 61 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 61 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 166 (accept_3_3 50 61 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 166 (Polychromatic418967fa.accept_11_5_6_1_1_988 49 61 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 166
  (Polychromatic418967fa.accept_9_3_7_4_1_53 48 61 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 166 (accept_3_3 47 61 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 166 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 61 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 61 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 166 (accept_3_3 44 61 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 61 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 166
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 61 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 166 (accept_3_3 41 61 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 166 (Polychromatic418967fa.accept_11_7_6_1_1_2182 40 61 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 61 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 166 (accept_3_3 38 61 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 166 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 61 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 166
  (Polychromatic418967fa.accept_16_4_13_6_1_4417 36 61 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 166 (accept_3_3 35 61 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 166 (Polychromatic418967fa.accept_18_16_7_4_1_3901 34 61 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 61 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 166 (accept_3_3 32 61 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 61 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 166
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 61 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 166 (accept_3_3 29 61 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 166 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 61 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 61 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 166 (accept_3_3 26 61 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 166 (Polychromatic418967fa.accept_10_5_1_6_1_672 25 61 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 166
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 61 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 166 (accept_3_3 23 61 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 166 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 61 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 61 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 166 (accept_3_3 20 61 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 61 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 166
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 61 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 166 (accept_3_3 17 61 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 166 (Polychromatic418967fa.accept_11_5_6_1_1_988 16 61 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 61 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 166 (accept_3_3 14 61 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 166 (Polychromatic418967fa.accept_18_13_7_4_1_2738 13 61 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 166
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 61 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 166 (accept_3_3 11 61 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 166 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 61 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 61 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 166 (accept_3_3 8 61 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 61 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 166
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 61 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 166 (accept_3_3 5 61 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  166 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 61 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 61 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 61 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 166 (accept_3_3 2 61 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 61 166 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 61 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61
  166))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 60 166 (allA_succ_of_accept 59 60 166
  (accept_3_3 59 60 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 60 166 2 29 30 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 60 166
  (Polychromatic418967fa.accept_7_1_4_5_1_35 57 60 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 60 166 2 28 30 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 60 166 (Polychromatic418967fa.accept_7_6_4_5_1_314 55 60 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 166 2 27 30 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 166 (accept_3_3 53 60 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 60 166 2 26 30 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 60 166 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 60 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 60 166 2 25 30 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 60 166
  (Polychromatic418967fa.accept_19_11_3_14_1_6375 49 60 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 60 166 2 24 30 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 60 166 (accept_3_3 47 60 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 60
  166 2 23 30 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  60 166 (Polychromatic418967fa.accept_19_7_3_14_1_5023 45 60 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 60 166 2 22 30 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 60 166 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 60 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 166 2 21 30 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 166 (accept_3_3 41 60 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 60 166 2 20 30 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 60 166
  (Polychromatic418967fa.accept_9_3_6_4_1_210 39 60 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 60 166 2 19 30 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 60 166 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 60 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 166 2 18 30 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 60 166 (accept_3_3 35 60 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 60 166 2 17 30 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 60 166 (Polychromatic418967fa.accept_13_7_8_10_1_2663 33 60 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 60 166 2 16 30 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 60 166
  (Polychromatic418967fa.accept_13_5_8_10_1_4363 31 60 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 60 166 2 15 30 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 60 166 (accept_3_3 29 60 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 60
  166 2 14 30 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  60 166 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 60 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 60 166 2 13 30 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 60 166 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 60 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 166 2 12 30 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 166 (accept_3_3 23 60 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 166 2 11 30 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 60 166
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 60 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 60 166 2 10 30 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 60 166 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 60 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 166 2 9 30 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 60 166 (accept_3_3 17 60 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 60 166 2 8 30 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 60 166 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 60 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 60 166 2 7 30 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 60 166 (Polychromatic418967fa.accept_7_6_4_5_1_314 13
  60 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 166 2 6 30 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 166 (accept_3_3 11
  60 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 166 2 5 30 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 60 166
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 60 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 60 166 2 4 30 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 60 166 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 60 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 166 2 3 30 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60 166 (accept_3_3 5 60 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 60 166 2 2 30 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 60 166 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 60 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 60 166 2 1 30 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 166 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 60
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  166)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 166 (allA_of_3_1 59 59 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 58 166 (allA_succ_of_accept 57 58 166
  (Polychromatic418967fa.accept_11_2_3_1_1_244 57 58 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 58 166 2 28 29 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 58 166 (Polychromatic418967fa.accept_13_3_6_10_1_2658 55 58 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 58 166 2 27 29 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 58 166 (accept_3_3 53 58 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 58 166 2 26 29 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 58 166 (Polychromatic418967fa.accept_13_12_6_10_1_667 51 58 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 58 166 2 25 29 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 58 166
  (Polychromatic418967fa.accept_14_7_2_12_1_1430 49 58 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 58 166 2 24 29 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 58 166 (accept_3_3 47 58 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 58
  166 2 23 29 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  58 166 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 58 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 58 166 2 22 29 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 58 166 (Polychromatic418967fa.accept_10_3_8_6_1_326 43 58 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 58 166 2 21 29 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 58 166 (accept_3_3 41 58 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 58 166 2 20 29 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 58 166
  (Polychromatic418967fa.accept_7_4_2_5_1_527 39 58 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 58 166 2 19 29 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 58 166 (Polychromatic418967fa.accept_19_18_1_14_1_4978 37 58 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 58 166 2 18 29 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 58 166 (accept_3_3 35 58 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 58 166 2 17 29 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 58 166 (Polychromatic418967fa.accept_10_3_8_6_1_326 33 58 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 58 166 2 16 29 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 58 166
  (Polychromatic418967fa.accept_7_3_2_5_1_147 31 58 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 58 166 2 15 29 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 58 166 (accept_3_3 29 58 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 58
  166 2 14 29 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  58 166 (Polychromatic418967fa.accept_15_12_13_1_1_3695 27 58 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 58 166 2 13 29 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 58 166 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 58 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 58 166 2 12 29 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 58 166 (accept_3_3 23 58 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 58 166 2 11 29 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 58 166
  (Polychromatic418967fa.accept_14_7_2_12_1_1430 21 58 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 58 166 2 10 29 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 58 166 (Polychromatic418967fa.accept_17_2_7_13_1_4163 19 58 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 58 166 2 9 29 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 58 166 (accept_3_3 17 58 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 58 166 2 8 29 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 58 166 (Polychromatic418967fa.accept_13_2_6_10_1_2703 15 58 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 58 166 2 7 29 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 58 166 (Polychromatic418967fa.accept_10_3_8_6_1_326 13
  58 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 58 166 2 6 29 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 58 166 (accept_3_3 11
  58 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 58 166 2 5 29 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 58 166
  (Polychromatic418967fa.accept_13_9_6_10_1_666 9 58 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 58 166 2 4 29 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 58 166 (Polychromatic418967fa.accept_14_7_2_12_1_1430 7 58 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 58 166 2 3 29 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 58 166 (accept_3_3 5 58 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 58 166 2 2 29 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 58 166 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 58 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 58 166 2 1 29 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 58 166 (Polychromatic418967fa.accept_21_1_16_19_1_3134
  1 58 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  166)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 166 (allA_succ_of_accept 56 57 166
  (accept_3_3 56 57 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 166
  (Polychromatic418967fa.accept_4_3_1_2_1_62 55 57 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 57 166 (Polychromatic418967fa.accept_11_10_2_1_1_1036 54 57 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 166 (accept_3_3 53 57 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 57 166 (Polychromatic418967fa.accept_7_3_1_5_1_44 52 57 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 51
  57 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 166 (accept_3_3 50 57
  166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 166 (Polychromatic418967fa.accept_6_1_3_4_1_1
  49 57 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 57 166
  (Polychromatic418967fa.accept_7_6_1_5_1_322 48 57 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 57 166 (accept_3_3 47 57 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  57 166 (Polychromatic418967fa.accept_7_4_1_5_1_540 46 57 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 57 166 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 57 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 166 (accept_3_3 44 57 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 57 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 57 166
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 57 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 57 166 (accept_3_3 41 57 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  57 166 (Polychromatic418967fa.accept_23_17_11_5_1_9195 40 57 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 57 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 57 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 166 (accept_3_3 38 57 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 57 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 57 166
  (Polychromatic418967fa.accept_11_3_2_1_1_994 36 57 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 57 166 (accept_3_3 35 57 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  57 166 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 57 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 57 166 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 57 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 166 (accept_3_3 32 57 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 57 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 57 166
  (Polychromatic418967fa.accept_12_6_9_10_1_565 30 57 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 57 166 (accept_3_3 29 57 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  57 166 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 57 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 57 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 57 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 166 (accept_3_3 26 57 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 57 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 57 166
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 57 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 57 166 (accept_3_3 23 57 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  57 166 (Polychromatic418967fa.accept_21_1_15_19_1_4491 22 57 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 57 166 (Polychromatic418967fa.accept_10_1_7_6_1_91 21 57 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 166 (accept_3_3 20 57 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 57 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 57 166
  (Polychromatic418967fa.accept_7_4_1_5_1_540 18 57 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 57 166 (accept_3_3 17 57 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  57 166 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 57 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 57 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 57 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 166 (accept_3_3 14 57 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 57 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 57 166
  (Polychromatic418967fa.accept_20_12_17_6_1_9194 12 57 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 57 166 (accept_3_3 11 57 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  57 166 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 57 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 57 166 (Polychromatic418967fa.accept_20_9_17_6_1_6098 9 57 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 166 (accept_3_3 8 57 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 57 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 166
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 57 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 166 (accept_3_3 5 57 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57
  166 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 57 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 57 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 57 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 166 (accept_3_3 2 57 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 57 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 57 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 166)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 166 (allA_of_3_1 56 56 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 55 166
  (allA_succ_of_accept 54 55 166 (Polychromatic418967fa.accept_10_4_5_6_1_651 54 55 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 166 (accept_3_3 53 55 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 55 166 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 55 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 51
  55 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 55 166 (accept_3_3 50 55
  166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 55 166 (Polychromatic418967fa.accept_4_1_3_2_1_3
  49 55 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 55 166
  (Polychromatic418967fa.accept_9_3_1_4_1_216 48 55 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 55 166 (accept_3_3 47 55 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  55 166 (Polychromatic418967fa.accept_7_4_6_5_1_141 46 55 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 55 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 55 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 55 166 (accept_3_3 44 55 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 166 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 55 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 166
  (Polychromatic418967fa.accept_9_6_1_4_1_474 42 55 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 166 (accept_3_3 41 55 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  55 166 (Polychromatic418967fa.accept_12_4_7_10_1_563 40 55 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 55 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 55 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 55 166 (accept_3_3 38 55 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 55 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 55 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 166
  (Polychromatic418967fa.accept_7_1_6_5_1_39 36 55 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 55 166 (accept_3_3 35 55 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  55 166 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 55 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 55 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 55 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 166 (accept_3_3 32 55 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 55 166 (Polychromatic418967fa.accept_10_1_5_6_1_649 31 55 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 55 166
  (Polychromatic418967fa.accept_9_3_1_4_1_216 30 55 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 55 166 (accept_3_3 29 55 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  55 166 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 55 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 55 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 55 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 166 (accept_3_3 26 55 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 55 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 55 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 55 166
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 55 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 55 166 (accept_3_3 23 55 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  55 166 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 55 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 55 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 55 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 55 166 (accept_3_3 20 55 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 55 166 (Polychromatic418967fa.accept_10_9_5_6_1_691 19 55 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 166
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 55 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 55 166 (accept_3_3 17 55 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  55 166 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 55 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 55 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 55 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 55 166 (accept_3_3 14 55 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 55 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 166
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 55 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 166 (accept_3_3 11 55 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  55 166 (Polychromatic418967fa.accept_20_10_15_6_1_2149 10 55 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 55 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 55 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 166 (accept_3_3 8 55 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 166 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 55 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 166
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 55 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 55 166 (accept_3_3 5 55 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 55
  166 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 55 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 55 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 166 (accept_3_3 2 55 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 55 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 166)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 54 166 (allA_succ_of_accept 53 54 166 (accept_3_3 53 54 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 54 166 2 26 27 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 54 166 (Polychromatic418967fa.accept_12_3_6_10_1_576 51 54 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 54 166 2 25 27 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 54 166
  (Polychromatic418967fa.accept_19_11_16_14_1_3553 49 54 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 54 166 2 24 27 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 54 166 (accept_3_3 47 54 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 54 166 2 23 27 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 54 166 (Polychromatic418967fa.accept_10_5_4_6_1_319 45 54 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 54 166 2 22 27 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 54 166 (Polychromatic418967fa.accept_19_5_16_14_1_2374
  43 54 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54 166 2 21 27 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 54 166 (accept_3_3 41
  54 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 54 166 2 20 27 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 54 166
  (Polychromatic418967fa.accept_12_3_6_10_1_576 39 54 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 54 166 2 19 27 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 54 166 (Polychromatic418967fa.accept_13_11_2_10_1_4399 37 54 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 166 2 18 27 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 166 (accept_3_3 35 54 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 54 166 2 17 27 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 54 166 (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 54 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 54 166 2 16 27 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 54 166
  (Polychromatic418967fa.accept_11_9_10_1_1_581 31 54 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 54 166 2 15 27 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 54 166 (accept_3_3 29 54 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54
  166 2 14 27 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  54 166 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 54 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 54 166 2 13 27 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 54 166 (Polychromatic418967fa.accept_10_5_4_6_1_319 25 54 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54 166 2 12 27 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 54 166 (accept_3_3 23 54 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 54 166 2 11 27 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 54 166
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 54 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 54 166 2 10 27 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 54 166 (Polychromatic418967fa.accept_13_6_2_10_1_1240 19 54 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 166 2 9 27 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 166 (accept_3_3 17 54 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 54 166 2 8 27 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 54 166 (Polychromatic418967fa.accept_10_5_4_6_1_319 15 54 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 54 166 2 7 27 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 54 166 (Polychromatic418967fa.accept_11_2_10_1_1_1017
  13 54 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 166 2 6 27 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 166 (accept_3_3 11
  54 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 54 166 2 5 27 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 54 166
  (Polychromatic418967fa.accept_11_9_10_1_1_581 9 54 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 54 166 2 4 27 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 54 166 (Polychromatic418967fa.accept_15_7_9_1_1_473 7 54 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 166 2 3 27 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 166 (accept_3_3 5 54 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 54 166 2 2 27 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 54 166 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 54 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 54 166 2 1 27 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 166 (Polychromatic418967fa.accept_20_1_14_6_1_4725 1
  54 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  166)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 166 (allA_of_3_1 53 53 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 52 166 (allA_succ_of_accept 51 52 166 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 52
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 52 166 2 25 26 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 52 166
  (Polychromatic418967fa.accept_12_1_4_10_1_209 49 52 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 52 166 2 24 26 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 52 166 (accept_3_3 47 52 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 52
  166 2 23 26 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  52 166 (Polychromatic418967fa.accept_16_13_4_6_1_2322 45 52 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 52 166 2 22 26 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 52 166 (Polychromatic418967fa.accept_7_1_3_5_1_33 43 52 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 52 166 2 21 26 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 52 166 (accept_3_3 41 52 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 52 166 2 20 26 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 52 166
  (Polychromatic418967fa.accept_9_3_7_4_1_53 39 52 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 52 166 2 19 26 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 52 166 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 52 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 52 166 2 18 26 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 52 166 (accept_3_3 35 52 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 52 166 2 17 26 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 52 166 (Polychromatic418967fa.accept_9_6_7_4_1_212 33 52 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 52 166 2 16 26 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 52 166
  (Polychromatic418967fa.accept_10_1_2_6_1_638 31 52 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 52 166 2 15 26 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 52 166 (accept_3_3 29 52 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 52
  166 2 14 26 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  52 166 (Polychromatic418967fa.accept_16_11_4_6_1_4422 27 52 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 52 166 2 13 26 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 52 166 (Polychromatic418967fa.accept_12_1_4_10_1_209 25 52 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 52 166 2 12 26 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 52 166 (accept_3_3 23 52 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 52 166 2 11 26 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 52 166
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 52 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 52 166 2 10 26 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 52 166 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 52 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 52 166 2 9 26 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 52 166 (accept_3_3 17 52 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 52 166 2 8 26 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 52 166 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 52 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 52 166 2 7 26 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 52 166 (Polychromatic418967fa.accept_12_1_4_10_1_209
  13 52 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 52 166 2 6 26 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 52 166 (accept_3_3 11
  52 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 52 166 2 5 26 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 52 166
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 52 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 52 166 2 4 26 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 52 166 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 52 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 52 166 2 3 26 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 52 166 (accept_3_3 5 52 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 52 166 2 2 26 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 52 166 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 52 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 52 166 2 1 26 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 52 166 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 52
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52
  166)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 166 (allA_succ_of_accept 50 51 166 (accept_3_3
  50 51 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 166
  (Polychromatic418967fa.accept_4_1_3_2_1_3 49 51 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 51 166 (Polychromatic418967fa.accept_9_3_6_4_1_210 48 51 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 166 (accept_3_3 47 51 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 51 166 (Polychromatic418967fa.accept_7_4_2_5_1_527 46 51 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 45
  51 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 166 (accept_3_3 44 51
  166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 166 (Polychromatic418967fa.accept_6_1_3_4_1_1
  43 51 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 51 166
  (Polychromatic418967fa.accept_10_2_1_6_1_634 42 51 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 51 166 (accept_3_3 41 51 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  51 166 (Polychromatic418967fa.accept_15_10_6_1_1_3707 40 51 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 51 166 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 51 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 166 (accept_3_3 38 51 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 51 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 51 166
  (Polychromatic418967fa.accept_16_4_3_6_1_6805 36 51 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 51 166 (accept_3_3 35 51 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  51 166 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 51 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 51 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 51 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 166 (accept_3_3 32 51 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 51 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 51 166
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 51 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 51 166 (accept_3_3 29 51 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  51 166 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 51 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 51 166 (Polychromatic418967fa.accept_10_7_1_6_1_673 27 51 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 166 (accept_3_3 26 51 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 51 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 51 166
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 51 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 51 166 (accept_3_3 23 51 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  51 166 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 51 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 51 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 51 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 166 (accept_3_3 20 51 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 51 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 51 166
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 51 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 51 166 (accept_3_3 17 51 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  51 166 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 51 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 51 166 (Polychromatic418967fa.accept_10_5_1_6_1_672 15 51 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 166 (accept_3_3 14 51 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 51 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 51 166
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 51 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 51 166 (accept_3_3 11 51 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  51 166 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 51 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 51 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 51 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 166 (accept_3_3 8 51 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 51 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51 166
  (Polychromatic418967fa.accept_11_6_7_1_1_564 6 51 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 166 (accept_3_3 5 51 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51
  166 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 51 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 51 166 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 51 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 166 (accept_3_3 2 51 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 51 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 51 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 166)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 166 (allA_of_3_1 50 50 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 49 166
  (allA_succ_of_accept 48 49 166 (Polychromatic418967fa.accept_15_3_4_1_1_1072 48 49 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 166 (accept_3_3 47 49 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 49 166 (Polychromatic418967fa.accept_18_10_13_4_1_5153 46 49 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 166
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 49 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 49 166 (accept_3_3 44 49 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  49 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 49 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 49 166 (Polychromatic418967fa.accept_15_12_4_1_1_3746 42 49 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 49 166 (accept_3_3 41 49 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 49 166 (Polychromatic418967fa.accept_12_4_1_10_1_221 40 49 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 166
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 49 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 49 166 (accept_3_3 38 49 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  49 166 (Polychromatic418967fa.accept_14_9_7_12_1_4034 37 49 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 49 166 (Polychromatic418967fa.accept_17_2_15_13_1_3034 36 49 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 49 166 (accept_3_3 35 49 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 49 166 (Polychromatic418967fa.accept_16_2_1_6_1_2342 34 49 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 166
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 49 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 49 166 (accept_3_3 32 49 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  49 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 49 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 49 166 (Polychromatic418967fa.accept_14_2_7_12_1_1485 30 49 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 166 (accept_3_3 29 49 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 49 166 (Polychromatic418967fa.accept_11_6_5_1_1_586 28 49 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 166
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 49 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 49 166 (accept_3_3 26 49 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  49 166 (Polychromatic418967fa.accept_10_5_9_6_1_697 25 49 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 49 166 (Polychromatic418967fa.accept_19_5_11_14_1_3654 24 49 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 166 (accept_3_3 23 49 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 166 (Polychromatic418967fa.accept_17_5_15_13_1_7936 22 49
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 166
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 49 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 49 166 (accept_3_3 20 49 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  49 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 49 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 49 166 (Polychromatic418967fa.accept_15_3_4_1_1_1072 18 49 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 166 (accept_3_3 17 49 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 49 166 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 49 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 166
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 49 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 49 166 (accept_3_3 14 49 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  49 166 (Polychromatic418967fa.accept_10_3_9_6_1_94 13 49 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 49 166 (Polychromatic418967fa.accept_15_12_4_1_1_3746 12 49 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 166 (accept_3_3 11 49 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 166 (Polychromatic418967fa.accept_18_10_13_4_1_5153 10 49
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 166
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 49 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 166 (accept_3_3 8 49 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49
  166 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 49 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 49 166 (Polychromatic418967fa.accept_11_6_5_1_1_586 6 49 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 166 (accept_3_3 5 49 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 49 166 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 49 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 49
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 166 (accept_3_3 2 49 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 166 (Polychromatic418967fa.accept_21_1_7_19_1_9193
  1 49 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49
  166))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 48 166 (allA_succ_of_accept 47 48 166 (accept_3_3 47
  48 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 48 166 2 23 24 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 48 166
  (Polychromatic418967fa.accept_13_6_9_10_1_1201 45 48 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 48 166 2 22 24 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 48 166 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 48 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 166 2 21 24 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 166 (accept_3_3 41 48 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 48 166 2 20 24 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 48 166 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 48 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 48 166 2 19 24 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 166
  (Polychromatic418967fa.accept_9_1_3_4_1_47 37 48 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 48 166 2 18 24 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 48 166 (accept_3_3 35 48 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48
  166 2 17 24 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  48 166 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 48 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 48 166 2 16 24 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 48 166 (Polychromatic418967fa.accept_19_12_10_14_1_6353 31 48 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 166 2 15 24 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 166 (accept_3_3 29 48 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 48 166 2 14 24 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 48 166
  (Polychromatic418967fa.accept_13_1_9_10_1_625 27 48 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 48 166 2 13 24 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 48 166 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 48 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 166 2 12 24 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 166 (accept_3_3 23 48 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48 166 2 11 24 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 48 166 (Polychromatic418967fa.accept_15_6_3_1_1_3678 21 48 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 48 166 2 10 24 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 48 166
  (Polychromatic418967fa.accept_9_1_3_4_1_47 19 48 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 48 166 2 9 24 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 48 166 (accept_3_3 17 48 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48
  166 2 8 24 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  48 166 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 48 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 48 166 2 7 24 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 48 166 (Polychromatic418967fa.accept_10_3_8_6_1_326 13 48 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 166 2 6 24 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 166 (accept_3_3 11 48 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48 166 2 5 24 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 48 166 (Polychromatic418967fa.accept_18_9_12_4_1_1659 9 48 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 48 166 2 4 24 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 48 166
  (Polychromatic418967fa.accept_9_7_3_4_1_218 7 48 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 48 166 2 3 24 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 48 166 (accept_3_3 5 48 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 166
  2 2 24 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 48
  166 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 48 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 48 166 2 1 24 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 48 166 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 48 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 48 166)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 166
  (allA_of_3_1 47 47 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 46 166 (allA_succ_of_accept 45 46 166
  (Polychromatic418967fa.accept_17_11_12_13_1_3030 45 46 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 46 166 2 22 23 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 46 166 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 46 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 46 166 2 21 23 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 46 166 (accept_3_3 41 46 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 46 166 2 20 23 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 46 166
  (Polychromatic418967fa.accept_9_3_1_4_1_216 39 46 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 46 166 2 19 23 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 46 166 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 46 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 46 166 2 18 23 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 46 166 (accept_3_3 35 46 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 46 166 2 17 23 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 46 166 (Polychromatic418967fa.accept_9_6_1_4_1_474 33 46 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 46 166 2 16 23 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 46 166
  (Polychromatic418967fa.accept_18_13_10_4_1_5150 31 46 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 46 166 2 15 23 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 46 166 (accept_3_3 29 46 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 46
  166 2 14 23 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  46 166 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 46 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 46 166 2 13 23 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 46 166 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 46 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 46 166 2 12 23 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 46 166 (accept_3_3 23 46 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 46 166 2 11 23 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 46 166
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 46 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 46 166 2 10 23 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 46 166 (Polychromatic418967fa.accept_22_19_2_12_1_9192 19 46 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 46 166 2 9 23 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 46 166 (accept_3_3 17 46 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 46 166 2 8 23 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 46 166 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 46 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 46 166 2 7 23 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 46 166 (Polychromatic418967fa.accept_7_6_4_5_1_314 13
  46 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 46 166 2 6 23 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 46 166 (accept_3_3 11
  46 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 46 166 2 5 23 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 46 166
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 46 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 46 166 2 4 23 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 46 166 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 46 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 46 166 2 3 23 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 46 166 (accept_3_3 5 46 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 46 166 2 2 23 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 46 166 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 46 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 46 166 2 1 23 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 46 166 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 46
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  166)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 166 (allA_succ_of_accept 44 45 166 (accept_3_3 44 45
  166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 166 (Polychromatic418967fa.accept_4_3_1_2_1_62
  43 45 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 45 166
  (Polychromatic418967fa.accept_12_6_9_10_1_565 42 45 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 45 166 (accept_3_3 41 45 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  45 166 (Polychromatic418967fa.accept_17_6_11_13_1_4180 40 45 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 45 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 45 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 166 (accept_3_3 38 45 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 45 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 166
  (Polychromatic418967fa.accept_7_1_3_5_1_33 36 45 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 45 166 (accept_3_3 35 45 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  45 166 (Polychromatic418967fa.accept_10_4_5_6_1_651 34 45 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 45 166 (Polychromatic418967fa.accept_14_5_3_12_1_324 33 45 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 166 (accept_3_3 32 45 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 45 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 45 166
  (Polychromatic418967fa.accept_7_2_3_5_1_34 30 45 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 45 166 (accept_3_3 29 45 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  45 166 (Polychromatic418967fa.accept_13_2_6_10_1_2703 28 45 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 45 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 45 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 166 (accept_3_3 26 45 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 45 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 45 166
  (Polychromatic418967fa.accept_10_4_5_6_1_651 24 45 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 45 166 (accept_3_3 23 45 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  45 166 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 45 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 45 166 (Polychromatic418967fa.accept_10_1_5_6_1_649 21 45 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 166 (accept_3_3 20 45 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 45 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 45 166
  (Polychromatic418967fa.accept_12_6_9_10_1_565 18 45 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 45 166 (accept_3_3 17 45 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  45 166 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 45 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 45 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 45 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 166 (accept_3_3 14 45 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 45 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 45 166
  (Polychromatic418967fa.accept_13_12_6_10_1_667 12 45 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 45 166 (accept_3_3 11 45 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  45 166 (Polychromatic418967fa.accept_19_10_7_14_1_3592 10 45 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 45 166 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 45 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 166 (accept_3_3 8 45 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 45 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 166
  (Polychromatic418967fa.accept_12_6_9_10_1_565 6 45 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 166 (accept_3_3 5 45 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45
  166 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 45 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 45 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 45 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 166 (accept_3_3 2 45 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 45 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 45 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 166))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  166 (allA_of_3_1 44 44 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 43 166 (allA_succ_of_accept 42 43 166
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 43 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 166 (accept_3_3 41 43 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 166 (Polychromatic418967fa.accept_12_4_7_10_1_563 40 43 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 43 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 166 (accept_3_3 38 43 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 43 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 166
  (Polychromatic418967fa.accept_16_4_11_6_1_5591 36 43 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 166 (accept_3_3 35 43 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 166 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 43 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 43 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 166 (accept_3_3 32 43 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 166 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 43 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 166
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 43 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 166 (accept_3_3 29 43 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 166 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 43 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 43 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 166 (accept_3_3 26 43 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 43 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 166
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 43 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 166 (accept_3_3 23 43 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 166 (Polychromatic418967fa.accept_17_5_9_13_1_1093 22 43 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 43 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 166 (accept_3_3 20 43 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 166 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 43 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 166
  (Polychromatic418967fa.accept_7_4_1_5_1_540 18 43 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 166 (accept_3_3 17 43 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 166 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 43 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 43 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 166 (accept_3_3 14 43 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 43 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 166
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 43 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 166 (accept_3_3 11 43 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 166 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 43 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 43 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 166 (accept_3_3 8 43 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 166 (Polychromatic418967fa.accept_10_7_3_6_1_644 7 43 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 166
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 43 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 166 (accept_3_3 5 43 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  166 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 43 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 43 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 166 (accept_3_3 2 43 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 43 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 166))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 166
  (allA_succ_of_accept 41 42 166 (accept_3_3 41 42 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 42
  166 2 20 21 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  42 166 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 42 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 42 166 2 19 21 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 42 166 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 42 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 166 2 18 21 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 166 (accept_3_3 35 42 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 42 166 2 17 21 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 42 166
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 42 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 42 166 2 16 21 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 42 166 (Polychromatic418967fa.accept_10_1_2_6_1_638 31 42 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 166 2 15 21 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 166 (accept_3_3 29 42 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 166 2 14 21 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 42 166 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 42 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 42 166 2 13 21 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 166
  (Polychromatic418967fa.accept_9_7_6_4_1_483 25 42 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 42 166 2 12 21 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 42 166 (accept_3_3 23 42 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42
  166 2 11 21 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  42 166 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 42 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 42 166 2 10 21 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 42 166 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 42 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 166 2 9 21 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 166 (accept_3_3 17 42 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 42 166 2 8 21 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 42 166 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 42 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 42 166 2 7 21 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 166
  (Polychromatic418967fa.accept_15_13_12_1_1_1841 13 42 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 42 166 2 6 21 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 42 166 (accept_3_3 11 42 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42
  166 2 5 21 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  42 166 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 42 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 42 166 2 4 21 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 42 166 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 42 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 166 2 3 21 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 166 (accept_3_3 5 42 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 42 166 2 2 21 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 42 166 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 42 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 42 166 2 1 21 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 166
  (Polychromatic418967fa.accept_9_1_6_4_1_49 1 42 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 42 166)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 166 (allA_of_3_1 41 41 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 40 166 (allA_succ_of_accept 39 40 166
  (Polychromatic418967fa.accept_11_6_7_1_1_564 39 40 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 40 166 2 19 20 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 40 166 (Polychromatic418967fa.accept_12_1_4_10_1_209 37 40 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 40 166 2 18 20 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 40 166 (accept_3_3 35 40 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 40 166 2 17 20 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 40 166 (Polychromatic418967fa.accept_22_11_18_12_1_7659 33 40
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 40 166 2 16 20 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 40 166
  (Polychromatic418967fa.accept_12_7_4_10_1_572 31 40 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 40 166 2 15 20 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 40 166 (accept_3_3 29 40 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 40
  166 2 14 20 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  40 166 (Polychromatic418967fa.accept_19_8_2_14_1_3640 27 40 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 40 166 2 13 20 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 40 166 (Polychromatic418967fa.accept_12_1_4_10_1_209 25 40 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 40 166 2 12 20 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 40 166 (accept_3_3 23 40 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 40 166 2 11 20 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 40 166
  (Polychromatic418967fa.accept_15_6_10_1_1_3675 21 40 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 40 166 2 10 20 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 40 166 (Polychromatic418967fa.accept_12_7_4_10_1_572 19 40 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 40 166 2 9 20 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 40 166 (accept_3_3 17 40 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 40 166 2 8 20 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 40 166 (Polychromatic418967fa.accept_22_15_18_12_1_9191 15 40 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 40 166 2 7 20 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 40 166
  (Polychromatic418967fa.accept_12_1_4_10_1_209 13 40 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 40 166 2 6 20 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 40 166 (accept_3_3 11 40 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40
  166 2 5 20 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  40 166 (Polychromatic418967fa.accept_13_9_1_10_1_647 9 40 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 40 166 2 4 20 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 40 166 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 40 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 40 166 2 3 20 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 40 166 (accept_3_3 5 40 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 40 166 2 2 20 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 40 166 (Polychromatic418967fa.accept_25_3_15_16_1_9190 3 40 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 40 166 2 1 20 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 40 166
  (Polychromatic418967fa.accept_12_1_4_10_1_209 1 40 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 40 166)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 166 (allA_succ_of_accept 38 39 166 (accept_3_3
  38 39 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 166
  (Polychromatic418967fa.accept_4_1_3_2_1_3 37 39 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 39 166 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 39 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 39 166 (accept_3_3 35 39 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 39 166 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 39 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 33
  39 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 166 (accept_3_3 32 39
  166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 166 (Polychromatic418967fa.accept_6_1_3_4_1_1
  31 39 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 39 166
  (Polychromatic418967fa.accept_7_2_4_5_1_313 30 39 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 39 166 (accept_3_3 29 39 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  39 166 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 39 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 39 166 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 39 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 166 (accept_3_3 26 39 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 39 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 39 166
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 39 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 39 166 (accept_3_3 23 39 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  39 166 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 39 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 39 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 39 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 166 (accept_3_3 20 39 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 39 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 39 166
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 39 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 39 166 (accept_3_3 17 39 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  39 166 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 39 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 39 166 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 39 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 166 (accept_3_3 14 39 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 39 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 39 166
  (Polychromatic418967fa.accept_21_12_18_19_1_7744 12 39 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 166 (accept_3_3 11 39 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 39 166 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 39 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 39 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 166 (accept_3_3 8 39 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 39
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39 166
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 39 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 166 (accept_3_3 5 39 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39
  166 (Polychromatic418967fa.accept_21_4_18_19_1_9189 4 39 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 166 (Polychromatic418967fa.accept_10_3_9_6_1_94 3 39 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 166 (accept_3_3 2 39 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 39 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 166))))))))))))))))))))))))))))))))))))))) (allB_succ
  38 166 (allA_of_3_1 38 38 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 37 166 (allA_succ_of_accept 36 37
  166 (Polychromatic418967fa.accept_15_6_7_1_1_93 36 37 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 37 166 (accept_3_3 35 37 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  37 166 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 37 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 37 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 37 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 166 (accept_3_3 32 37 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 37 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 166
  (Polychromatic418967fa.accept_9_3_1_4_1_216 30 37 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 166 (accept_3_3 29 37 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  37 166 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 37 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 37 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 166 (accept_3_3 26 37 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 166 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 37 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 166
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 37 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 166 (accept_3_3 23 37 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 166 (Polychromatic418967fa.accept_19_3_18_14_1_5020 22 37 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 37 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 166 (accept_3_3 20 37 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 37 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 166
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 37 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 166 (accept_3_3 17 37 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  37 166 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 37 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 37 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 166 (accept_3_3 14 37 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 166 (Polychromatic418967fa.accept_10_3_7_6_1_659 13 37 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 166
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 37 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 166 (accept_3_3 11 37 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  37 166 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 37 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 37 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 166 (accept_3_3 8 37 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 37 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 166
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 37 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 166 (accept_3_3 5 37 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  166 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 37 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 37 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 166 (accept_3_3 2 37 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 166 (Polychromatic418967fa.accept_10_1_7_6_1_91 1 37 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 166))))))))))))))))))))))))))))))))))))) (allB_succ 36 166
  (allA_succ_of_accept 35 36 166 (accept_3_3 35 36 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 36
  166 2 17 18 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  36 166 (Polychromatic418967fa.accept_15_3_6_1_1_1834 33 36 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 36 166 2 16 18 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 36 166 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 36 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 166 2 15 18 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 166 (accept_3_3 29 36 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 166 2 14 18 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 36 166
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 36 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 36 166 2 13 18 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 36 166 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 36 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 166 2 12 18 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 166 (accept_3_3 23 36 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36 166 2 11 18 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 36 166 (Polychromatic418967fa.accept_16_5_4_6_1_3349 21 36 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 36 166 2 10 18 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 166
  (Polychromatic418967fa.accept_16_3_4_6_1_6798 19 36 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 36 166 2 9 18 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 36 166 (accept_3_3 17 36 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36
  166 2 8 18 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  36 166 (Polychromatic418967fa.accept_17_15_2_13_1_4153 15 36 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 36 166 2 7 18 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 36 166 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 36 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 166 2 6 18 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 166 (accept_3_3 11 36 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 36 166 2 5 18 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 36 166 (Polychromatic418967fa.accept_15_9_6_1_1_493 9 36 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 36 166 2 4 18 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 36 166
  (Polychromatic418967fa.accept_15_7_6_1_1_1091 7 36 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 36 166 2 3 18 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 36 166 (accept_3_3 5 36 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 166
  2 2 18 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 36
  166 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 36 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 36 166 2 1 18 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 36 166 (Polychromatic418967fa.accept_17_1_2_13_1_2026 1 36 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 36 166)))))))))))))))))))))))))))))))))))) (allB_succ 35 166 (allA_of_3_1 35
  35 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 34 166 (allA_succ_of_accept 33 34 166
  (Polychromatic418967fa.accept_9_6_7_4_1_212 33 34 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 34 166 2 16 17 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 34 166 (Polychromatic418967fa.accept_13_5_8_10_1_4363 31 34 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 34 166 2 15 17 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 34 166 (accept_3_3 29 34 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 34 166 2 14 17 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 34 166 (Polychromatic418967fa.accept_14_13_6_12_1_3126 27 34
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 34 166 2 13 17 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 34 166
  (Polychromatic418967fa.accept_7_4_6_5_1_141 25 34 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 34 166 2 12 17 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 34 166 (accept_3_3 23 34 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 34
  166 2 11 17 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  34 166 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 34 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 34 166 2 10 17 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 34 166 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 34 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 34 166 2 9 17 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 34 166 (accept_3_3 17 34 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 34 166 2 8 17 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 34 166 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 34 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 34 166 2 7 17 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 34 166
  (Polychromatic418967fa.accept_14_13_6_12_1_3126 13 34 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 34 166 2 6 17 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 34 166 (accept_3_3 11 34 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 34
  166 2 5 17 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  34 166 (Polychromatic418967fa.accept_16_9_2_6_1_4434 9 34 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 34 166 2 4 17 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 34 166 (Polychromatic418967fa.accept_13_7_8_10_1_2663 7 34 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 34 166 2 3 17 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 34 166 (accept_3_3 5 34 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 34 166 2 2 17 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 34 166 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 34 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 34 166 2 1 17 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 34 166
  (Polychromatic418967fa.accept_7_1_6_5_1_39 1 34 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 34 166)))))))))))))))))))))))))))))))))) (allB_succ 33 166 (allA_succ_of_accept 32 33 166 (accept_3_3 32 33
  166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 166 (Polychromatic418967fa.accept_4_3_1_2_1_62
  31 33 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 166
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 33 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 33 166 (accept_3_3 29 33 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  33 166 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 33 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 33 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 33 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 166 (accept_3_3 26 33 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 33 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 33 166
  (Polychromatic418967fa.accept_14_10_5_12_1_3995 24 33 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 33 166 (accept_3_3 23 33 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  33 166 (Polychromatic418967fa.accept_21_1_12_19_1_7721 22 33 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 33 166 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 33 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 166 (accept_3_3 20 33 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 33 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 166
  (Polychromatic418967fa.accept_10_8_3_6_1_685 18 33 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 33 166 (accept_3_3 17 33 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  33 166 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 33 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 33 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 33 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 166 (accept_3_3 14 33 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 33 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 166
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 33 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 33 166 (accept_3_3 11 33 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  33 166 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 33 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 33 166 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 33 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 166 (accept_3_3 8 33 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 33 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 166
  (Polychromatic418967fa.accept_12_6_9_10_1_565 6 33 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 166 (accept_3_3 5 33 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33
  166 (Polychromatic418967fa.accept_13_4_7_10_1_1200 4 33 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 33 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 33 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 166 (accept_3_3 2 33 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 33 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 166))))))))))))))))))))))))))))))))) (allB_succ 32
  166 (allA_of_3_1 32 32 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 31 166 (allA_succ_of_accept 30 31 166
  (Polychromatic418967fa.accept_7_2_3_5_1_34 30 31 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 31 166 (accept_3_3 29 31 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  31 166 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 31 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 31 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 31 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 166 (accept_3_3 26 31 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 31 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 166
  (Polychromatic418967fa.accept_26_24_5_10_1_9188 24 31 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 166 (accept_3_3 23 31 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  31 166 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 31 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 31 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 31 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 166 (accept_3_3 20 31 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 166 (Polychromatic418967fa.accept_13_6_5_10_1_1213 19 31 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 166
  (Polychromatic418967fa.accept_17_1_14_13_1_7966 18 31 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 166 (accept_3_3 17 31 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 166 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 31 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 31 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 166 (accept_3_3 14 31 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 31 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 166
  (Polychromatic418967fa.accept_10_2_1_6_1_634 12 31 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 166 (accept_3_3 11 31 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 166 (Polychromatic418967fa.accept_11_10_9_1_1_2186 10 31 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 31 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 166 (accept_3_3 8 31 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 166 (Polychromatic418967fa.accept_10_7_1_6_1_673 7 31 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 166
  (Polychromatic418967fa.accept_13_6_5_10_1_1213 6 31 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 166 (accept_3_3 5 31 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  166 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 31 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 31 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 31 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 166 (accept_3_3 2 31 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 31 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 166))))))))))))))))))))))))))))))) (allB_succ 30 166
  (allA_succ_of_accept 29 30 166 (accept_3_3 29 30 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30
  166 2 14 15 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  30 166 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 30 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 30 166 2 13 15 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 30 166 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 30 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 166 2 12 15 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 166 (accept_3_3 23 30 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 166 2 11 15 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 30 166
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 30 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 30 166 2 10 15 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 30 166 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 30 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 166 2 9 15 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 166 (accept_3_3 17 30 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 30 166 2 8 15 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 30 166 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 30 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 30 166 2 7 15 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 166 (Polychromatic418967fa.accept_24_13_6_22_1_2345
  13 30 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 166 2 6 15 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 166 (accept_3_3 11
  30 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 166 2 5 15 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 30 166
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 30 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 30 166 2 4 15 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 30 166 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 30 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 166 2 3 15 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 166 (accept_3_3 5 30 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 30 166 2 2 15 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 30 166 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 30 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 30 166 2 1 15 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 166 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 30
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 166))))))))))))))))))))))))))))))
  (allB_succ 29 166 (allA_of_3_1 29 29 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 28 166
  (allA_succ_of_accept 27 28 166 (Polychromatic418967fa.accept_11_5_6_1_1_988 27 28 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 28 166 2 13 14 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 28 166 (Polychromatic418967fa.accept_9_7_1_4_1_217 25
  28 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 28 166 2 12 14 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 28 166 (accept_3_3 23
  28 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 28 166 2 11 14 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 28 166
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 28 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 28 166 2 10 14 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 28 166 (Polychromatic418967fa.accept_12_7_4_10_1_572 19 28 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 28 166 2 9 14 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 28 166 (accept_3_3 17 28 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 28 166 2 8 14 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 28 166 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 28 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 28 166 2 7 14 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 28 166 (Polychromatic418967fa.accept_10_3_8_6_1_326 13
  28 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 28 166 2 6 14 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 28 166 (accept_3_3 11
  28 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 28 166 2 5 14 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 28 166
  (Polychromatic418967fa.accept_21_9_7_19_1_9187 9 28 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 28 166 2 4 14 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 28 166 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 28 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 28 166 2 3 14 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 28 166 (accept_3_3 5 28 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 28 166 2 2 14 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 28 166 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 28 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 28 166 2 1 14 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 28 166 (Polychromatic418967fa.accept_12_1_4_10_1_209 1
  28 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 166))))))))))))))))))))))))))))
  (allB_succ 27 166 (allA_succ_of_accept 26 27 166 (accept_3_3 26 27 166 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 27 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 166 (Polychromatic418967fa.accept_13_11_1_10_1_648 24 27
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 166 (accept_3_3 23 27 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 166 (Polychromatic418967fa.accept_7_1_6_5_1_39 22
  27 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 166
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 27 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 27 166 (accept_3_3 20 27 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  27 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 27 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 27 166 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 27 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 166 (accept_3_3 17 27 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 166 (Polychromatic418967fa.accept_20_16_7_6_1_7815 16 27 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 166
  (Polychromatic418967fa.accept_7_1_6_5_1_39 15 27 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 27 166 (accept_3_3 14 27 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  27 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 27 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 27 166 (Polychromatic418967fa.accept_18_12_9_4_1_2740 12 27 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 166 (accept_3_3 11 27 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 166 (Polychromatic418967fa.accept_25_10_2_16_1_9186 10 27
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 166
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 27 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 27 166 (accept_3_3 8 27 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27
  166 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 27 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 27 166 (Polychromatic418967fa.accept_11_6_5_1_1_586 6 27 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 166 (accept_3_3 5 27 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 27 166 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 27 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 166 (Polychromatic418967fa.accept_10_3_7_6_1_659 3
  27 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 166 (accept_3_3 2 27 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 27
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 166)))))))))))))))))))))))))))
  (allB_succ 26 166 (allA_of_3_1 26 26 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 25 166
  (allA_succ_of_accept 24 25 166 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 25 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 166 (accept_3_3 23 25 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 25 166 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 25 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 21
  25 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 166 (accept_3_3 20 25
  166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 166 (Polychromatic418967fa.accept_4_3_1_2_1_62
  19 25 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 166
  (Polychromatic418967fa.accept_16_2_9_6_1_4441 18 25 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 166 (accept_3_3 17 25 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 166 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 25 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 25 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 25 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 166 (accept_3_3 14 25 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 166 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 25 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 166
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 25 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 166 (accept_3_3 11 25 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  25 166 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 25 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 25 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 25 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 166 (accept_3_3 8 25 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 25 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 166
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 25 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 166 (accept_3_3 5 25 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25
  166 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 25 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 25 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 25 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 166 (accept_3_3 2 25 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 25 166 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 25 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 166))))))))))))))))))))))))) (allB_succ 24 166
  (allA_succ_of_accept 23 24 166 (accept_3_3 23 24 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24
  166 2 11 12 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  24 166 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 24 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 24 166 2 10 12 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 24 166 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 24 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 166 2 9 12 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 166 (accept_3_3 17 24 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 24 166 2 8 12 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 24 166 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 24 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 24 166 2 7 12 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 166
  (Polychromatic418967fa.accept_19_13_5_14_1_3530 13 24 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 24 166 2 6 12 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 24 166 (accept_3_3 11 24 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24
  166 2 5 12 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  24 166 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 24 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 24 166 2 4 12 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 24 166 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 24 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 166 2 3 12 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24 166 (accept_3_3 5 24 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 24 166 2 2 12 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 24 166 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 24 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 24 166 2 1 12 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 166
  (Polychromatic418967fa.accept_7_1_3_5_1_33 1 24 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 24 166)))))))))))))))))))))))) (allB_succ 23 166 (allA_of_3_1 23 23 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 22 166 (allA_succ_of_accept 21 22 166 (Polychromatic418967fa.accept_10_1_2_6_1_638 21 22 166
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 22 166 2 10 11 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 22 166
  (Polychromatic418967fa.accept_13_6_9_10_1_1201 19 22 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 22 166 2 9 11 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 22 166 (accept_3_3 17 22 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 22
  166 2 8 11 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  22 166 (Polychromatic418967fa.accept_17_15_5_13_1_6626 15 22 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 22 166 2 7 11 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 22 166 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 22 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 22 166 2 6 11 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 22 166 (accept_3_3 11 22 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 22 166 2 5 11 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 22 166 (Polychromatic418967fa.accept_15_9_7_1_1_1075 9 22 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 22 166 2 4 11 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 22 166
  (Polychromatic418967fa.accept_19_7_3_14_1_5023 7 22 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 22 166 2 3 11 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 22 166 (accept_3_3 5 22 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 22 166
  2 2 11 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 22
  166 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 22 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 22 166 2 1 11 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 22 166 (Polychromatic418967fa.accept_10_1_2_6_1_638 1 22 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 22 166)))))))))))))))))))))) (allB_succ 21 166 (allA_succ_of_accept 20 21
  166 (accept_3_3 20 21 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 166
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 21 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 21 166 (Polychromatic418967fa.accept_12_6_9_10_1_565 18 21 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 166 (accept_3_3 17 21 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 21 166 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 21 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 15
  21 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 166 (accept_3_3 14 21
  166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 166 (Polychromatic418967fa.accept_6_1_3_4_1_1
  13 21 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 166
  (Polychromatic418967fa.accept_10_2_1_6_1_634 12 21 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 21 166 (accept_3_3 11 21 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  21 166 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 21 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 21 166 (Polychromatic418967fa.accept_11_9_10_1_1_581 9 21 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 166 (accept_3_3 8 21 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 21 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21 166
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 21 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 166 (accept_3_3 5 21 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21
  166 (Polychromatic418967fa.accept_13_4_8_10_1_671 4 21 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 21 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 21 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 166 (accept_3_3 2 21 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 21 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 166))))))))))))))))))))) (allB_succ 20 166
  (allA_of_3_1 20 20 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 19 166 (allA_succ_of_accept 18 19 166
  (Polychromatic418967fa.accept_13_5_6_10_1_2659 18 19 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 166 (accept_3_3 17 19 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 166 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 19 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 19 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 166 (accept_3_3 14 19 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 19 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 166
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 19 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 166 (accept_3_3 11 19 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 166 (Polychromatic418967fa.accept_14_10_5_12_1_3995 10 19 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 19 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 166 (accept_3_3 8 19 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 166 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 19 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 166
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 19 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 166 (accept_3_3 5 19 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  166 (Polychromatic418967fa.accept_11_4_8_1_1_1047 4 19 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 19 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 19 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 166 (accept_3_3 2 19 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 19 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 19 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 166))))))))))))))))))) (allB_succ 18 166
  (allA_succ_of_accept 17 18 166 (accept_3_3 17 18 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18
  166 2 8 9 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  18 166 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 18 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 18 166 2 7 9 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 18 166 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 18 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 166 2 6 9 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 166 (accept_3_3 11 18 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 18 166 2 5 9 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 18 166 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 18 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 166 2 4 9 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 166
  (Polychromatic418967fa.accept_19_7_18_14_1_9185 7 18 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 18 166 2 3 9 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 18 166 (accept_3_3 5 18 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 166
  2 2 9 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18 166
  (Polychromatic418967fa.accept_10_3_8_6_1_326 3 18 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 18 166 2 1 9 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 18 166 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 18 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 18 166)))))))))))))))))) (allB_succ 17 166 (allA_of_3_1 17 17 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 16 166 (allA_succ_of_accept 15 16 166
  (Polychromatic418967fa.accept_9_6_7_4_1_212 15 16 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 16 166 2 7 8 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 16 166 (Polychromatic418967fa.accept_12_1_4_10_1_209 13 16 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 16 166 2 6 8 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 16 166 (accept_3_3 11 16 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 16 166 2 5 8 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 16 166 (Polychromatic418967fa.accept_17_9_16_13_1_6636 9 16 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 16 166 2 4 8 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 16 166 (Polychromatic418967fa.accept_12_7_4_10_1_572 7
  16 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 16 166 2 3 8 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 16 166 (accept_3_3 5 16
  166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 16 166 2 2 8 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 16 166
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 16 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 16 166 2 1 8 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 16 166 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 16 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 16 166)))))))))))))))) (allB_succ 15 166 (allA_succ_of_accept 14 15 166
  (accept_3_3 14 15 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 166
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 15 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 15 166 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 15 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 166 (accept_3_3 11 15 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 15 166 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 15 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 15
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 166 (accept_3_3 8 15 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 15
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 166
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 15 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 166 (accept_3_3 5 15 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15
  166 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 15 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 15 166 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 15 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 166 (accept_3_3 2 15 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 15 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 15 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 166))))))))))))))) (allB_succ 14 166 (allA_of_3_1 14 14 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 166 (allA_succ_of_accept 12 13 166
  (Polychromatic418967fa.accept_15_12_13_1_1_3695 12 13 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 166 (accept_3_3 11 13 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 166 (Polychromatic418967fa.accept_11_10_2_1_1_1036 10 13 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 13 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 166 (accept_3_3 8 13 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 13 166 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 166
  (Polychromatic418967fa.accept_14_6_13_12_1_810 6 13 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 166 (accept_3_3 5 13 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  166 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 13 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 13 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 166 (accept_3_3 2 13 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 166 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 13 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 166))))))))))))) (allB_succ 12 166 (allA_succ_of_accept 11 12
  166 (accept_3_3 11 12 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 12 166 2 5 6 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 12 166
  (Polychromatic418967fa.accept_13_9_12_10_1_242 9 12 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 12 166 2 4 6 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 12 166 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 12 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 166 2 3 6 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 166 (accept_3_3 5 12 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 12 166 2 2 6 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 12 166 (Polychromatic418967fa.accept_25_3_12_16_1_9184 3 12 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 166 2 1 6 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 166 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 12
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 166)))))))))))) (allB_succ 11 166
  (allA_of_3_1 11 11 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 10 166 (allA_succ_of_accept 9 10 166
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 10 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 10 166 2 4 5 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 10 166 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 10 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 10 166 2 3 5 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 10 166 (accept_3_3 5 10 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 10 166 2 2 5 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 10 166 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 10 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 10 166 2 1 5 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 10 166 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 10
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 166)))))))))) (allB_succ 9 166
  (allA_succ_of_accept 8 9 166 (accept_3_3 8 9 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 166
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 9 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 9 166 (Polychromatic418967fa.accept_12_6_9_10_1_565 6 9 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 166 (accept_3_3 5 9 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 9 166 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 9 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 166 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 9
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 166 (accept_3_3 2 9 166
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 166 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 9
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 166))))))))) (allB_succ 8 166
  (allA_of_3_1 8 8 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 7 166 (allA_succ_of_accept 6 7 166
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 7 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 166 (accept_3_3 5 7 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 166
  (Polychromatic418967fa.accept_12_4_7_10_1_563 4 7 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 166 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 7 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 166 (accept_3_3 2 7 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 7 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 166))))))) (allB_succ 6 166 (allA_succ_of_accept 5 6 166
  (accept_3_3 5 6 166 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 166 2 2 3 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 166
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 6 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 6 166 2 1 3 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 166 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 6 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 6 166)))))) (allB_succ 5 166 (allA_of_3_1 5 5 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 4 166 (allA_succ_of_accept 3 4 166 (Polychromatic418967fa.accept_15_3_4_1_1_1072 3 4
  166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 4 166 2 1 2 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 4 166
  (Polychromatic418967fa.accept_7_1_4_5_1_35 1 4 166 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 166)))) (allB_succ 3 166 (allA_succ_of_accept 2 3 166 (accept_3_3 2 3 166 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 166 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 3 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 166))) (allB_succ 2 166 (allA_of_3_1 2 2 166 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  166))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


