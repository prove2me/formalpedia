-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch180
-- name    : Polychromatic418967fa_Branch180
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:20:04.28832+00:00
-- url     : https://prove2.me/theorems/749df0e5-e361-45a2-a23d-b588451b9609
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch180_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_180 : allB 180 180 :=
  allB_succ' 2 179 180 (Eq.refl Bool.true) (allA_succ_of_accept 1 179 180 (accept_3_4 1 179 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 179 180)) (allB_succ' 3 178 180 (Eq.refl Bool.true) (allA_succ_of_gcd 2 178 180 2 1 89
  90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 178 180
  (Polychromatic418967fa.accept_7_1_3_5_1_33 1 178 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 178 180))) (allB_succ' 4 177 180 (Eq.refl Bool.true) (allA_succ_of_gcd 3 177 180 3 1 59 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 177 180
  (Polychromatic418967fa.accept_21_2_9_12_1_4040 2 177 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 177 180 (Polychromatic418967fa.accept_13_1_8_11_1_724 1 177 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 177 180)))) (allB_succ' 5 176 180 (Eq.refl Bool.true) (allA_succ_of_gcd 4
  176 180 4 1 44 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  3 176 180 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 176 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 176 180 2 1 88 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 176 180 (accept_3_4 1 176 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 176
  180))))) (allB_succ' 6 175 180 (Eq.refl Bool.true) (allA_succ_of_gcd 5 175 180 5 1 35 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 175 180
  (Polychromatic418967fa.accept_13_4_6_11_1_2017 4 175 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 175 180 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 175 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 175 180 (accept_3_5 2 175 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 175 180 (Polychromatic418967fa.accept_21_1_7_12_1_1465 1 175 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 175 180)))))) (allB_succ' 7 174 180 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 174 180 6 1 29 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 174 180 (Polychromatic418967fa.accept_21_5_6_12_1_7091 5 174 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 174 180 2 2 87 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 174 180 3 1 58 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 174 180 2 1 87 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 174 180 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 174 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174 180))))))) (allB_succ' 8 173 180 (Eq.refl
  Bool.true) (allA_succ_of_accept 7 173 180 (accept_3_4 7 173 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 173 180 (Polychromatic418967fa.accept_13_6_4_11_1_282 6 173 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 173 180 (Polychromatic418967fa.accept_23_5_12_19_1_10372 5 173
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 173 180 (accept_3_4 4 173 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 173 180 (Polychromatic418967fa.accept_14_3_5_12_1_4000
  3 173 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 173 180
  (Polychromatic418967fa.accept_13_2_4_11_1_2003 2 173 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 173 180 (accept_3_4 1 173 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 173
  180)))))))) (allB_succ' 9 172 180 (Eq.refl Bool.true) (allA_succ_of_gcd 8 172 180 4 2 43 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 172 180
  (Polychromatic418967fa.accept_13_7_3_11_1_280 7 172 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 172 180 2 3 86 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 172 180 (accept_3_5 5 172 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 172
  180 4 1 43 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  172 180 (Polychromatic418967fa.accept_11_3_7_4_1_1133 3 172 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 172 180 2 1 86 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 172 180 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 172 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 172 180))))))))) (allB_succ' 10 171 180 (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 171 180 9 1 19 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 171 180 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 171 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 180 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 171 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 171 180 3 2 57 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 171 180
  (Polychromatic418967fa.accept_14_5_3_12_1_324 5 171 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 171 180 (Polychromatic418967fa.accept_13_4_2_11_1_733 4 171 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 171 180 3 1 57 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 171 180 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 171 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 180
  (Polychromatic418967fa.accept_7_1_3_5_1_33 1 171 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 171 180)))))))))) (allB_succ' 11 170 180 (Eq.refl Bool.true) (allA_succ_of_gcd 10 170 180 10 1 17 18
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 170 180
  (Polychromatic418967fa.accept_13_9_1_11_1_275 9 170 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 170 180 2 4 85 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 170 180 (accept_3_4 7 170 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 170
  180 2 3 85 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 170
  180 5 1 34 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 170
  180 2 2 85 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  170 180 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 170 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 170 180 2 1 85 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 170 180 (accept_3_4 1 170 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 170
  180))))))))))) (allB_succ' 12 169 180 (Eq.refl Bool.true) (allA_succ_of_accept 11 169 180 (accept_3_5 11 169 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 169 180 (Polychromatic418967fa.accept_7_3_1_5_1_44 10
  169 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 169 180
  (Polychromatic418967fa.accept_17_9_16_10_1_362 9 169 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 169 180 (accept_3_5 8 169 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  169 180 (Polychromatic418967fa.accept_17_7_16_10_1_1849 7 169 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 169 180 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 169 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 169 180 (accept_3_5 5 169 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 169 180 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 169 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 169 180
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 169 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 169 180 (accept_3_5 2 169 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  169 180 (Polychromatic418967fa.accept_19_1_17_9_1_2150 1 169 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 169 180)))))))))))) (allB_succ' 13 168 180 (Eq.refl Bool.true) (allA_succ_of_gcd 12 168 180 12 1
  14 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 168 180
  (Polychromatic418967fa.accept_16_11_8_4_1_2234 11 168 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 168 180 2 5 84 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 168 180 3 3 56 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 168 180 4 2 42 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 168 180 (Polychromatic418967fa.accept_11_7_3_4_1_729 7 168 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 168 180 6 1 28 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 168 180 (Polychromatic418967fa.accept_16_5_8_4_1_5418 5 168 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 168 180 4 1 42 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 168 180 3 1 56 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 168 180 2 1 84 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 168 180
  (Polychromatic418967fa.accept_13_1_12_11_1_728 1 168 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 168 180))))))))))))) (allB_succ' 14 167 180 (Eq.refl Bool.true) (allA_succ_of_accept 13 167 180 (accept_3_4
  13 167 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 167 180
  (Polychromatic418967fa.accept_16_12_7_4_1_687 12 167 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 167 180 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 167 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 167 180 (accept_3_4 10 167 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 167 180 (Polychromatic418967fa.accept_11_9_2_4_1_707 9 167 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 167 180 (Polychromatic418967fa.accept_7_1_6_5_1_39 8
  167 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 167 180 (accept_3_4 7 167
  180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 167 180
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 6 167 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 167 180 (Polychromatic418967fa.accept_17_5_14_10_1_2831 5 167 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 167 180 (accept_3_4 4 167 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 167 180 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 167 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 167 180 (Polychromatic418967fa.accept_19_2_15_9_1_7318
  2 167 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 167 180 (accept_3_4 1
  167 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 167 180)))))))))))))) (allB_succ' 15 166 180 (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 166 180 2 7 83 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 166 180 (Polychromatic418967fa.accept_16_13_6_4_1_3277 13 166 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 166 180 2 6 83 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 166 180 (accept_3_5 11 166 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 166 180 2 5 83 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 166 180
  (Polychromatic418967fa.accept_17_9_13_10_1_1825 9 166 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 166 180 2 4 83 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 166 180 (Polychromatic418967fa.accept_21_7_19_12_1_5579 7 166 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 166 180 2 3 83 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 166 180 (accept_3_5 5 166 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 166 180 2 2 83 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 166 180 (Polychromatic418967fa.accept_13_3_10_11_1_1293 3 166 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 166 180 2 1 83 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 166 180
  (Polychromatic418967fa.accept_13_1_10_11_1_1280 1 166 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 166 180))))))))))))))) (allB_succ' 16 165 180 (Eq.refl Bool.true) (allA_succ_of_gcd 15 165 180 15 1 11 12
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 165 180
  (Polychromatic418967fa.accept_13_1_9_11_1_703 14 165 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 165 180 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 165 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 165 180 3 4 55 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 165 180
  (Polychromatic418967fa.accept_21_11_18_12_1_1494 11 165 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 165 180 5 2 33 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 9 165 180 3 3 55 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 8 165 180 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 165 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 180
  (Polychromatic418967fa.accept_13_7_9_11_1_705 7 165 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 165 180 3 2 55 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 165 180 5 1 33 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 165 180 (Polychromatic418967fa.accept_19_4_13_9_1_5968 4 165 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 165 180 3 1 55 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 165 180 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 165 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 180
  (Polychromatic418967fa.accept_7_1_4_5_1_35 1 165 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 165 180)))))))))))))))) (allB_succ' 17 164 180 (Eq.refl Bool.true) (allA_succ_of_gcd 16 164 180 4 4 41 45
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 164 180
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 164 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 164 180 2 7 82 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 164 180 (accept_3_4 13 164 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12
  164 180 4 3 41 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  11 164 180 (Polychromatic418967fa.accept_22_11_10_4_1_10153 11 164 180 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 164 180 2 5 82 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 164 180 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 164 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 164 180 4 2 41 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 164 180 (accept_3_4 7 164 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 164 180 2 3 82 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 164 180 (Polychromatic418967fa.accept_11_5_10_4_1_1157
  5 164 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 164 180 4 1 41 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 164 180
  (Polychromatic418967fa.accept_13_3_8_11_1_1906 3 164 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 164 180 2 1 82 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 164 180 (accept_3_4 1 164 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 164
  180))))))))))))))))) (allB_succ' 18 163 180 (Eq.refl Bool.true) (allA_succ_of_accept 17 163 180 (accept_3_5 17 163 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 163 180
  (Polychromatic418967fa.accept_13_3_7_11_1_1904 16 163 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 163 180 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 163 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 163 180 (accept_3_5 14 163 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 163 180 (Polychromatic418967fa.accept_11_2_9_4_1_310 13 163 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 163 180
  (Polychromatic418967fa.accept_13_12_7_11_1_1935 12 163 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 163 180 (accept_3_5 11 163 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 163 180 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 163 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 163 180 (Polychromatic418967fa.accept_13_9_7_11_1_1292 9 163
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 163 180 (accept_3_5 8 163 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 163 180 (Polychromatic418967fa.accept_8_7_3_4_1_404 7
  163 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 163 180
  (Polychromatic418967fa.accept_16_6_3_4_1_6624 6 163 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 163 180 (accept_3_5 5 163 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  163 180 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 163 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 163 180 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 163 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 163 180 (accept_3_5 2 163 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 163 180 (Polychromatic418967fa.accept_13_1_7_11_1_702 1 163 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 163 180)))))))))))))))))) (allB_succ' 19 162 180
  (Eq.refl Bool.true) (allA_succ_of_gcd 18 162 180 18 1 9 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 162 180 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 162 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 162 180 2 8 81 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 162 180 3 5 54 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 162 180 2 7 81 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 162 180
  (Polychromatic418967fa.accept_7_6_1_5_1_322 13 162 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 162 180 6 2 27 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 162 180 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 162 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 162 180 2 5 81 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 162 180 9 1 18 20 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 162 180 2 4 81 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 162 180 (Polychromatic418967fa.accept_11_7_8_4_1_718 7
  162 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 162 180 6 1 27 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 162 180
  (Polychromatic418967fa.accept_13_5_6_11_1_1933 5 162 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 162 180 2 2 81 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 162 180 3 1 54 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 162 180 2 1 81 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 162 180 (Polychromatic418967fa.accept_11_1_8_4_1_717 1 162 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 162 180))))))))))))))))))) (allB_succ' 20 161 180 (Eq.refl Bool.true)
  (allA_succ_of_accept 19 161 180 (accept_3_4 19 161 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 161 180 (Polychromatic418967fa.accept_21_18_14_12_1_4075 18 161 180 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 17 161 180 (Polychromatic418967fa.accept_25_17_11_5_1_4675 17 161 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 161 180 (accept_3_4 16 161 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 161 180
  (Polychromatic418967fa.accept_17_15_8_10_1_2886 15 161 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 161 180 (Polychromatic418967fa.accept_11_3_7_4_1_1133 14 161 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 161 180 (accept_3_4 13 161 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 161 180 (Polychromatic418967fa.accept_16_12_1_4_1_5403 12 161
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 161 180
  (Polychromatic418967fa.accept_21_11_14_12_1_5471 11 161 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 161 180 (accept_3_4 10 161 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 161 180 (Polychromatic418967fa.accept_14_9_7_12_1_4034 9 161 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 161 180 (Polychromatic418967fa.accept_11_8_7_4_1_3011 8 161 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 161 180 (accept_3_4 7 161 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 161 180 (Polychromatic418967fa.accept_13_6_5_11_1_1971
  6 161 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 161 180
  (Polychromatic418967fa.accept_8_5_1_4_1_628 5 161 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 161 180 (accept_3_4 4 161 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  161 180 (Polychromatic418967fa.accept_11_3_7_4_1_1133 3 161 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 161 180 (Polychromatic418967fa.accept_14_2_7_12_1_1485 2 161 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 161 180 (accept_3_4 1 161 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 161 180)))))))))))))))))))) (allB_succ' 21 160 180 (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 160 180 20 1 8 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 160 180 (Polychromatic418967fa.accept_13_6_4_11_1_282 19 160 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 160 180 2 9 80 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 160 180 (accept_3_5 17 160 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 160 180 4 4 40 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 160 180 5 3 32 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 160 180 2 7 80 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 160 180 (Polychromatic418967fa.accept_11_2_6_4_1_3028 13 160
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 160 180 4 3 40 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 160 180 (accept_3_5 11
  160 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 160 180 10 1 16 18 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 160 180
  (Polychromatic418967fa.accept_21_9_13_12_1_10185 9 160 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 160 180 4 2 40 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 160 180 (Polychromatic418967fa.accept_13_7_4_11_1_1967 7 160 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 160 180 2 3 80 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 160 180 5 1 32 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 160 180 4 1 40 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 160 180 (Polychromatic418967fa.accept_17_3_7_10_1_3948
  3 160 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 160 180 2 1 80 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 160 180
  (Polychromatic418967fa.accept_7_1_6_5_1_39 1 160 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 160 180))))))))))))))))))))) (allB_succ' 22 159 180 (Eq.refl Bool.true) (allA_succ_of_gcd 21 159 180 3 7 53
  60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 159 180
  (Polychromatic418967fa.accept_13_7_3_11_1_280 20 159 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 159 180 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 159 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 159 180 3 6 53 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 159 180 (Polychromatic418967fa.accept_14_3_5_12_1_4000
  17 159 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 159 180
  (Polychromatic418967fa.accept_17_16_6_10_1_1863 16 159 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 159 180 3 5 53 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 159 180 (Polychromatic418967fa.accept_13_1_3_11_1_1289 14 159 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 180
  (Polychromatic418967fa.accept_19_13_7_9_1_3322 13 159 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 159 180 3 4 53 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 159 180 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 159 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 159 180 (Polychromatic418967fa.accept_11_10_5_4_1_711 10 159
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 159 180 3 3 53 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 159 180
  (Polychromatic418967fa.accept_13_8_3_11_1_3467 8 159 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 159 180 (Polychromatic418967fa.accept_13_7_3_11_1_280 7 159 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 159 180 3 2 53 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 159 180 (Polychromatic418967fa.accept_13_5_3_11_1_1288 5 159 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 159 180
  (Polychromatic418967fa.accept_17_4_6_10_1_5164 4 159 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 159 180 3 1 53 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 159 180 (Polychromatic418967fa.accept_13_2_3_11_1_1287 2 159 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 180 (Polychromatic418967fa.accept_13_1_3_11_1_1289 1 159
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 159 180)))))))))))))))))))))) (allB_succ'
  23 158 180 (Eq.refl Bool.true) (allA_succ_of_gcd 22 158 180 2 11 79 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 158 180
  (Polychromatic418967fa.accept_27_21_23_18_1_10371 21 158 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 158 180 2 10 79 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 158 180 (accept_3_4 19 158 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 158 180 2 9 79 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 158 180 (Polychromatic418967fa.accept_13_4_2_11_1_733 17 158 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 158 180 2 8 79 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 158 180 (Polychromatic418967fa.accept_7_1_4_5_1_35 15
  158 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 158 180 2 7 79 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 158 180 (accept_3_4 13
  158 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 158 180 2 6 79 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 158 180
  (Polychromatic418967fa.accept_25_11_8_5_1_4696 11 158 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 158 180 2 5 79 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 158 180 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 158 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 158 180 2 4 79 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 158 180 (accept_3_4 7 158 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 158 180 2 3 79 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 158 180 (Polychromatic418967fa.accept_21_5_11_12_1_1479 5 158 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 158 180 2 2 79 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 158 180
  (Polychromatic418967fa.accept_13_3_2_11_1_1999 3 158 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 158 180 2 1 79 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 158 180 (accept_3_4 1 158 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158
  180))))))))))))))))))))))) (allB_succ' 24 157 180 (Eq.refl Bool.true) (allA_succ_of_accept 23 157 180 (accept_3_5 23
  157 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 157 180
  (Polychromatic418967fa.accept_7_1_3_5_1_33 22 157 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 157 180 (Polychromatic418967fa.accept_13_8_1_11_1_1284 21 157 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 157 180 (accept_3_5 20 157 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 157 180 (Polychromatic418967fa.accept_14_5_3_12_1_324 19 157 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 157 180
  (Polychromatic418967fa.accept_11_7_3_4_1_729 18 157 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 157 180 (accept_3_5 17 157 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 157 180 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 157 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 157 180 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 157 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 157 180 (accept_3_5 14 157 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 157 180 (Polychromatic418967fa.accept_19_13_5_9_1_3318 13 157 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 157 180
  (Polychromatic418967fa.accept_13_12_1_11_1_1917 12 157 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 157 180 (accept_3_5 11 157 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 157 180 (Polychromatic418967fa.accept_13_10_1_11_1_1961 10 157 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 157 180 (Polychromatic418967fa.accept_7_2_3_5_1_34 9
  157 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 157 180 (accept_3_5 8 157
  180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 157 180
  (Polychromatic418967fa.accept_11_7_3_4_1_729 7 157 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 157 180 (Polychromatic418967fa.accept_16_6_13_4_1_643 6 157 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 157 180 (accept_3_5 5 157 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 157 180 (Polychromatic418967fa.accept_19_4_5_9_1_8855 4 157 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 157 180 (Polychromatic418967fa.accept_13_3_1_11_1_1268
  3 157 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 157 180 (accept_3_5 2
  157 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 157 180
  (Polychromatic418967fa.accept_7_1_3_5_1_33 1 157 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 157 180)))))))))))))))))))))))) (allB_succ' 25 156 180 (Eq.refl Bool.true) (allA_succ_of_gcd 24 156 180 12 2
  13 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 156 180
  (Polychromatic418967fa.accept_16_7_12_4_1_1347 23 156 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 156 180 2 11 78 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 156 180 3 7 52 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 156 180 4 5 39 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 156 180 (Polychromatic418967fa.accept_16_3_12_4_1_170 19 156 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 156 180 6 3 26 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 156 180
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 156 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 156 180 4 4 39 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 156 180 3 5 52 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 156 180 2 7 78 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 156 180 (Polychromatic418967fa.accept_16_13_12_4_1_4323 13 156 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 156 180 12 1 13 15 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 156 180
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 156 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 156 180 2 5 78 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 156 180 3 3 52 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 156 180 4 2 39 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 156 180 (Polychromatic418967fa.accept_14_7_2_12_1_1430 7 156 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 156 180 6 1 26 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 156 180 (Polychromatic418967fa.accept_16_5_12_4_1_4325 5 156 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 156 180 4 1 39 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 156 180 3 1 52 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 156 180 2 1 78 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 156 180
  (Polychromatic418967fa.accept_16_1_12_4_1_695 1 156 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 156 180))))))))))))))))))))))))) (allB_succ' 26 155 180 (Eq.refl Bool.true) (allA_succ_of_gcd 25 155 180 5 5
  31 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 155 180
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 155 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 155 180 (Polychromatic418967fa.accept_8_7_3_4_1_404 23 155 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 155 180 (accept_3_4 22 155 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 155 180 (Polychromatic418967fa.accept_23_21_17_19_1_10313 21 155 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 155 180 5 4 31 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 155 180 (accept_3_4 19 155 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 155 180 (Polychromatic418967fa.accept_7_4_1_5_1_540
  18 155 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 155 180
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 155 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 155 180 (accept_3_4 16 155 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15
  155 180 5 3 31 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  14 155 180 (Polychromatic418967fa.accept_13_1_12_11_1_728 14 155 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 155 180 (accept_3_4 13 155 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 155 180 (Polychromatic418967fa.accept_16_12_11_4_1_1359 12 155 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 155 180 (Polychromatic418967fa.accept_7_4_1_5_1_540
  11 155 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 155 180 5 2 31 36
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 155 180
  (Polychromatic418967fa.accept_16_9_11_4_1_3194 9 155 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 155 180 (Polychromatic418967fa.accept_11_8_1_4_1_2318 8 155 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 155 180 (accept_3_4 7 155 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 155 180 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 155 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 155 180 5 1 31 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 155 180 (accept_3_4 4 155 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 155 180 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 155 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 155 180
  (Polychromatic418967fa.accept_23_2_17_19_1_10370 2 155 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 155 180 (accept_3_4 1 155 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one
  155 180)))))))))))))))))))))))))) (allB_succ' 27 154 180 (Eq.refl Bool.true) (allA_succ_of_gcd 26 154 180 2 13 77 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 154 180
  (Polychromatic418967fa.accept_21_4_7_12_1_10320 25 154 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 154 180 2 12 77 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 154 180 (accept_3_5 23 154 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 154 180 2 11 77 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 154 180 (Polychromatic418967fa.accept_25_21_4_5_1_10369 21 154 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 154 180 2 10 77 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 154 180
  (Polychromatic418967fa.accept_21_19_7_12_1_5507 19 154 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 154 180 2 9 77 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 154 180 (accept_3_5 17 154 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 154 180 2 8 77 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 154 180 (Polychromatic418967fa.accept_19_15_2_9_1_10357 15 154 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 154 180 2 7 77 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 154 180
  (Polychromatic418967fa.accept_27_13_19_18_1_10368 13 154 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 154 180 2 6 77 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 154 180 (accept_3_5 11 154 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 154 180 2 5 77 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 154 180 (Polychromatic418967fa.accept_17_9_1_10_1_2859 9 154 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 154 180 2 4 77 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 154 180 (Polychromatic418967fa.accept_17_7_1_10_1_2836 7 154 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 154 180 2 3 77 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 154 180 (accept_3_5 5 154 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 154 180 2 2 77 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 154 180 (Polychromatic418967fa.accept_21_3_7_12_1_8725
  3 154 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 154 180 2 1 77 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 154 180
  (Polychromatic418967fa.accept_19_1_2_9_1_3314 1 154 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 154 180))))))))))))))))))))))))))) (allB_succ' 28 153 180 (Eq.refl Bool.true) (allA_succ_of_gcd 27 153 180 9
  3 17 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 153
  180 (Polychromatic418967fa.accept_21_5_6_12_1_7091 26 153 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 153 180 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 153 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 153 180 3 8 51 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 153 180
  (Polychromatic418967fa.accept_21_2_6_12_1_5506 23 153 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 153 180 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 153 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 153 180 3 7 51 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 153 180 (Polychromatic418967fa.accept_14_6_13_12_1_810
  20 153 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 180
  (Polychromatic418967fa.accept_21_19_6_12_1_7089 19 153 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 153 180 9 2 17 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 153 180 (Polychromatic418967fa.accept_13_4_10_11_1_1908 17 153 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 153 180
  (Polychromatic418967fa.accept_11_5_10_4_1_1157 16 153 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 153 180 3 5 51 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 153 180 (Polychromatic418967fa.accept_13_1_10_11_1_1280 14 153 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 180 (Polychromatic418967fa.accept_8_5_1_4_1_628
  13 153 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 153 180 3 4 51 60
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 153 180
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 153 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 153 180 (Polychromatic418967fa.accept_19_10_1_9_1_10161 10 153 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 153 180 9 1 17 20 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 153 180 (Polychromatic418967fa.accept_7_1_6_5_1_39 8
  153 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 180
  (Polychromatic418967fa.accept_21_7_6_12_1_10316 7 153 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 153 180 3 2 51 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 153 180 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 153 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 180 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 153 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 153 180 3 1 51 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 153 180
  (Polychromatic418967fa.accept_13_2_10_11_1_1276 2 153 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 153 180 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 153 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 153 180)))))))))))))))))))))))))))) (allB_succ' 29 152 180 (Eq.refl
  Bool.true) (allA_succ_of_gcd 28 152 180 4 7 38 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 152 180 (Polychromatic418967fa.accept_13_1_9_11_1_703 27 152 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 152 180 2 13 76 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 152 180 (accept_3_4 25 152 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 152 180 4 6 38 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 152 180
  (Polychromatic418967fa.accept_16_7_8_4_1_689 23 152 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 152 180 2 11 76 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 152 180 (Polychromatic418967fa.accept_13_8_9_11_1_1265 21 152 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 152 180 4 5 38 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 152 180 (accept_3_4 19 152 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 152 180 2 9 76 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 152 180
  (Polychromatic418967fa.accept_16_1_8_4_1_4334 17 152 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 152 180 4 4 38 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 152 180 (Polychromatic418967fa.accept_13_2_9_11_1_258 15 152 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 152 180 2 7 76 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 152 180 (accept_3_4 13 152 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 152 180 4 3 38 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 152 180 (Polychromatic418967fa.accept_16_11_8_4_1_2234 11 152
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 152 180 2 5 76 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 152 180
  (Polychromatic418967fa.accept_16_9_8_4_1_1354 9 152 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 152 180 4 2 38 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 152 180 (accept_3_4 7 152 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 152
  180 2 3 76 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  152 180 (Polychromatic418967fa.accept_16_5_8_4_1_5418 5 152 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 152 180 4 1 38 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 152 180 (Polychromatic418967fa.accept_16_3_8_4_1_3279 3 152 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 152 180 2 1 76 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 152 180 (accept_3_4 1 152 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 152 180))))))))))))))))))))))))))))) (allB_succ' 30 151 180 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 151 180 (accept_3_5 29 151 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 151 180 (Polychromatic418967fa.accept_16_12_7_4_1_687 28 151 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 151 180 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 151 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 151 180 (accept_3_5 26 151 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 151 180 (Polychromatic418967fa.accept_17_8_15_10_1_10367 25 151 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 151 180
  (Polychromatic418967fa.accept_16_8_7_4_1_2217 24 151 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 151 180 (accept_3_5 23 151 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 151 180 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 151 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 151 180 (Polychromatic418967fa.accept_17_4_15_10_1_5139 21 151 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 151 180 (accept_3_5 20 151 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 151 180 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 151 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 151 180
  (Polychromatic418967fa.accept_11_7_8_4_1_718 18 151 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 151 180 (accept_3_5 17 151 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 151 180 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 151 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 151 180 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 151 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 151 180 (accept_3_5 14 151 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 151 180 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 151 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 151 180
  (Polychromatic418967fa.accept_11_1_8_4_1_717 12 151 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 151 180 (accept_3_5 11 151 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 151 180 (Polychromatic418967fa.accept_13_10_8_11_1_1985 10 151 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 151 180 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 151 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 151 180 (accept_3_5 8 151 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 151 180 (Polychromatic418967fa.accept_11_7_8_4_1_718 7 151 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 151 180
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 151 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 151 180 (accept_3_5 5 151 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  151 180 (Polychromatic418967fa.accept_13_4_8_11_1_1937 4 151 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 151 180 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 151 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 151 180 (accept_3_5 2 151 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 151 180 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 151 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 151 180)))))))))))))))))))))))))))))) (allB_succ' 31 150
  180 (Eq.refl Bool.true) (allA_succ_of_gcd 30 150 180 30 1 5 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 150 180 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 150 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 150 180 2 14 75 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 150 180 3 9 50 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 150 180 2 13 75 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 150 180 5 5 30 36
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 150 180 6 4 25 30
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 150 180
  (Polychromatic418967fa.accept_7_2_3_5_1_34 23 150 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 150 180 2 11 75 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 150 180 3 7 50 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 150 180 10 2 15 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 150 180 (Polychromatic418967fa.accept_11_8_7_4_1_3011 19 150 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 150 180 6 3 25 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 150 180
  (Polychromatic418967fa.accept_13_4_7_11_1_1981 17 150 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 150 180 2 8 75 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 150 180 15 1 10 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 150 180 2 7 75 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 150 180 (Polychromatic418967fa.accept_16_13_6_4_1_3277 13 150 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 150 180 6 2 25 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 150 180
  (Polychromatic418967fa.accept_16_11_6_4_1_2228 11 150 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 150 180 10 1 15 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 150 180 3 3 50 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 150 180 2 4 75 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 150 180 (Polychromatic418967fa.accept_17_7_14_10_1_1846 7 150 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 150 180 6 1 25 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 150 180 5 1 30 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 150 180 2 2 75 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 150 180 3 1 50 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 150 180 2 1 75 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 150 180
  (Polychromatic418967fa.accept_7_1_3_5_1_33 1 150 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 150 180))))))))))))))))))))))))))))))) (allB_succ' 32 149 180 (Eq.refl Bool.true) (allA_succ_of_accept 31
  149 180 (accept_3_4 31 149 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 149 180
  (Polychromatic418967fa.accept_13_4_6_11_1_2017 30 149 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 149 180 (Polychromatic418967fa.accept_19_10_16_9_1_10157 29 149 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 149 180 (accept_3_4 28 149 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 149 180 (Polychromatic418967fa.accept_19_8_16_9_1_8847 27 149 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 149 180
  (Polychromatic418967fa.accept_17_9_13_10_1_1825 26 149 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 149 180 (accept_3_4 25 149 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 149 180 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 149 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 149 180 (Polychromatic418967fa.accept_19_4_16_9_1_10315 23 149
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 149 180 (accept_3_4 22 149
  180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 149 180
  (Polychromatic418967fa.accept_13_8_6_11_1_1979 21 149 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 149 180 (Polychromatic418967fa.accept_17_3_13_10_1_3935 20 149 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 149 180 (accept_3_4 19 149 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 149 180 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 149 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 149 180
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 149 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 149 180 (accept_3_4 16 149 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 149 180 (Polychromatic418967fa.accept_16_15_5_4_1_6678 15 149 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 149 180 (Polychromatic418967fa.accept_17_14_13_10_1_3936 14 149 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 149 180 (accept_3_4 13 149 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 149 180 (Polychromatic418967fa.accept_16_12_5_4_1_3275 12 149
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 149 180
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 149 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 149 180 (accept_3_4 10 149 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  149 180 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 149 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 149 180 (Polychromatic418967fa.accept_13_8_6_11_1_1979 8 149 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 149 180 (accept_3_4 7 149 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 149 180 (Polychromatic418967fa.accept_16_6_5_4_1_4330 6 149 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 149 180
  (Polychromatic418967fa.accept_13_5_6_11_1_1933 5 149 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 149 180 (accept_3_4 4 149 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  149 180 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 149 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 149 180 (Polychromatic418967fa.accept_11_2_6_4_1_3028 2 149 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 149 180 (accept_3_4 1 149 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 149 180)))))))))))))))))))))))))))))))) (allB_succ' 33 148 180 (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 148 180 4 8 37 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 148 180 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 148 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 148 180 2 15 74 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 148 180 (accept_3_5 29 148 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 148 180 4 7 37 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 148 180 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 148 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 148 180 2 13 74 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 148 180
  (Polychromatic418967fa.accept_7_4_1_5_1_540 25 148 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 148 180 4 6 37 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 148 180 (accept_3_5 23 148 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  148 180 2 11 74 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 148 180 (Polychromatic418967fa.accept_11_10_5_4_1_711 21 148 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 148 180 4 5 37 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 148 180 (Polychromatic418967fa.accept_13_6_5_11_1_1971
  19 148 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 148 180 2 9 74 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 148 180
  (accept_3_5 17 148 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 148 180 4 4 37 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 148 180
  (Polychromatic418967fa.accept_21_15_1_12_1_10209 15 148 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 148 180 2 7 74 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 148 180 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 148 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 148 180 4 3 37 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 148 180 (accept_3_5 11 148 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 148 180 2 5 74 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 148 180
  (Polychromatic418967fa.accept_21_9_1_12_1_3984 9 148 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 148 180 4 2 37 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 148 180 (Polychromatic418967fa.accept_13_7_5_11_1_1927 7 148 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 148 180 2 3 74 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 148 180 (accept_3_5 5 148 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 148 180 4 1 37 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 148 180 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 148 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 148 180 2 1 74 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 148 180 (Polychromatic418967fa.accept_24_1_4_12_1_10366
  1 148 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 148
  180))))))))))))))))))))))))))))))))) (allB_succ' 34 147 180 (Eq.refl Bool.true) (allA_succ_of_gcd 33 147 180 3 11 49
  60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 147 180
  (Polychromatic418967fa.accept_13_6_4_11_1_282 32 147 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 147 180 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 147 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 147 180 3 10 49 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 147 180
  (Polychromatic418967fa.accept_23_6_9_19_1_10365 29 147 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 147 180 (Polychromatic418967fa.accept_13_2_4_11_1_2003 28 147 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 147 180 3 9 49 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 147 180
  (Polychromatic418967fa.accept_25_1_22_5_1_10364 26 147 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 147 180 (Polychromatic418967fa.accept_13_12_4_11_1_1925 25 147 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 147 180 3 8 49 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 147 180
  (Polychromatic418967fa.accept_8_7_3_4_1_404 23 147 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 147 180 (Polychromatic418967fa.accept_16_6_3_4_1_6624 22 147 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 147 180 3 7 49 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 147 180 (Polychromatic418967fa.accept_13_7_4_11_1_1967
  20 147 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 180
  (Polychromatic418967fa.accept_13_6_4_11_1_282 19 147 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 147 180 3 6 49 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 147 180 (Polychromatic418967fa.accept_16_1_3_4_1_665 17 147 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 147 180 (Polychromatic418967fa.accept_14_2_7_12_1_1485 16 147
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 147 180 3 5 49 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 147 180
  (Polychromatic418967fa.accept_22_14_15_4_1_8623 14 147 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 147 180 (Polychromatic418967fa.accept_23_13_9_19_1_10298 13 147 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 147 180 3 4 49 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 147 180
  (Polychromatic418967fa.accept_19_11_14_9_1_4599 11 147 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 147 180 (Polychromatic418967fa.accept_13_10_4_11_1_1969 10 147 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 147 180 3 3 49 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 147 180
  (Polychromatic418967fa.accept_13_8_4_11_1_3469 8 147 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 147 180 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 147 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 147 180 3 2 49 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 147 180 (Polychromatic418967fa.accept_14_5_7_12_1_4006 5 147 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 147 180
  (Polychromatic418967fa.accept_17_4_11_10_1_5167 4 147 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 147 180 3 1 49 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 147 180 (Polychromatic418967fa.accept_13_2_4_11_1_2003 2 147 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 180 (Polychromatic418967fa.accept_16_1_3_4_1_665 1 147 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 147 180))))))))))))))))))))))))))))))))))
  (allB_succ' 35 146 180 (Eq.refl Bool.true) (allA_succ_of_gcd 34 146 180 2 17 73 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 146 180
  (Polychromatic418967fa.accept_13_7_3_11_1_280 33 146 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 146 180 2 16 73 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 146 180 (accept_3_4 31 146 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 146 180 2 15 73 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 146 180 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 146 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 146 180 2 14 73 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 146 180
  (Polychromatic418967fa.accept_13_1_3_11_1_1289 27 146 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 146 180 2 13 73 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 146 180 (accept_3_4 25 146 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 146 180 2 12 73 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 146 180 (Polychromatic418967fa.accept_13_10_3_11_1_1923 23 146 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 146 180 2 11 73 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 146 180
  (Polychromatic418967fa.accept_13_8_3_11_1_3467 21 146 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 146 180 2 10 73 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 146 180 (accept_3_4 19 146 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 146 180 2 9 73 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 146 180 (Polychromatic418967fa.accept_19_17_13_9_1_5970 17 146 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 146 180 2 8 73 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 146 180
  (Polychromatic418967fa.accept_7_1_6_5_1_39 15 146 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 146 180 2 7 73 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 146 180 (accept_3_4 13 146 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12
  146 180 2 6 73 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  11 146 180 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 146 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 146 180 2 5 73 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 146 180 (Polychromatic418967fa.accept_21_9_20_12_1_5564 9 146 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 146 180 2 4 73 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 146 180 (accept_3_4 7 146 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 146 180 2 3 73 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 146 180 (Polychromatic418967fa.accept_13_5_3_11_1_1288 5 146 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 146 180 2 2 73 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 146 180
  (Polychromatic418967fa.accept_19_3_13_9_1_8876 3 146 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 146 180 2 1 73 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 146 180 (accept_3_4 1 146 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146
  180))))))))))))))))))))))))))))))))))) (allB_succ' 36 145 180 (Eq.refl Bool.true) (allA_succ_of_gcd 35 145 180 5 7 29
  36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 145 180
  (Polychromatic418967fa.accept_22_12_13_4_1_10363 34 145 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 145 180 (Polychromatic418967fa.accept_17_16_9_10_1_3962 33 145 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 145 180 (accept_3_5 32 145 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 145 180 (Polychromatic418967fa.accept_11_9_2_4_1_707 31 145
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 145 180 5 6 29 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 145 180 (accept_3_5 29
  145 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 145 180
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 28 145 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 145 180 (Polychromatic418967fa.accept_21_6_19_12_1_3981 27 145 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 145 180 (accept_3_5 26 145 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 25 145 180 5 5 29 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 145 180 (Polychromatic418967fa.accept_14_10_5_12_1_3995 24 145
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 145 180 (accept_3_5 23 145
  180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 145 180
  (Polychromatic418967fa.accept_13_9_2_11_1_1964 22 145 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 145 180 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 145 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 145 180 5 4 29 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 145 180 (Polychromatic418967fa.accept_16_3_1_4_1_5426
  19 145 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 145 180
  (Polychromatic418967fa.accept_17_1_9_10_1_1864 18 145 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 145 180 (accept_3_5 17 145 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 145 180 (Polychromatic418967fa.accept_13_3_2_11_1_1999 16 145 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 145 180 5 3 29 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 145 180 (accept_3_5 14 145 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 145 180 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 145 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 145 180 (Polychromatic418967fa.accept_16_12_1_4_1_5403 12 145
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 145 180 (accept_3_5 11 145
  180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 145 180 5 2 29 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 145 180
  (Polychromatic418967fa.accept_11_9_2_4_1_707 9 145 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 145 180 (accept_3_5 8 145 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  145 180 (Polychromatic418967fa.accept_14_7_5_12_1_1439 7 145 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 145 180 (Polychromatic418967fa.accept_11_6_2_4_1_1703 6 145 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 145 180 5 1 29 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 145 180 (Polychromatic418967fa.accept_13_4_2_11_1_733 4
  145 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 145 180
  (Polychromatic418967fa.accept_13_3_2_11_1_1999 3 145 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 145 180 (accept_3_5 2 145 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  145 180 (Polychromatic418967fa.accept_17_1_9_10_1_1864 1 145 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 145 180)))))))))))))))))))))))))))))))))))) (allB_succ' 37 144 180 (Eq.refl Bool.true)
  (allA_succ_of_gcd 36 144 180 36 1 4 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 144 180 (Polychromatic418967fa.accept_13_9_1_11_1_275 35 144 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 144 180 2 17 72 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 144 180 3 11 48 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 144 180 4 8 36 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 144 180
  (Polychromatic418967fa.accept_25_6_19_5_1_10362 31 144 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 144 180 6 5 24 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 144 180 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 144 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 144 180 4 7 36 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 144 180 9 3 16 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 144 180 2 13 72 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 144 180
  (Polychromatic418967fa.accept_13_12_1_11_1_1917 25 144 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 144 180 12 2 12 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 144 180 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 144 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 144 180 2 11 72 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 144 180 3 7 48 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 144 180 4 5 36 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 144 180
  (Polychromatic418967fa.accept_11_8_1_4_1_2318 19 144 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 144 180 18 1 8 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 144 180 (Polychromatic418967fa.accept_19_17_11_9_1_2141 17 144 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 144 180 4 4 36 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 144 180 3 5 48 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 144 180 2 7 72 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 144 180
  (Polychromatic418967fa.accept_7_6_4_5_1_314 13 144 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 144 180 12 1 12 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 144 180 (Polychromatic418967fa.accept_21_11_18_12_1_1494 11 144 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 144 180 2 5 72 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 144 180 9 1 16 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 144 180 4 2 36 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 144 180
  (Polychromatic418967fa.accept_13_7_1_11_1_732 7 144 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 144 180 6 1 24 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 144 180 (Polychromatic418967fa.accept_21_5_18_12_1_5531 5 144 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 144 180 4 1 36 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 144 180 3 1 48 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 144 180 2 1 72 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 144 180 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 144 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144 180)))))))))))))))))))))))))))))))))))))
  (allB_succ' 38 143 180 (Eq.refl Bool.true) (allA_succ_of_accept 37 143 180 (accept_3_4 37 143 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 143 180 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 143 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 143 180
  (Polychromatic418967fa.accept_8_3_7_4_1_42 35 143 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 143 180 (accept_3_4 34 143 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 143 180 (Polychromatic418967fa.accept_14_5_3_12_1_324 33 143 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 143 180 (Polychromatic418967fa.accept_19_13_10_9_1_5995 32 143 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 143 180 (accept_3_4 31 143 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 143 180 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 143 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 143 180
  (Polychromatic418967fa.accept_7_1_3_5_1_33 29 143 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 143 180 (accept_3_4 28 143 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 143 180 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 143 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 143 180 (Polychromatic418967fa.accept_19_7_10_9_1_2162 26 143 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 143 180 (accept_3_4 25 143 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 143 180 (Polychromatic418967fa.accept_16_8_15_4_1_5402 24 143
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 143 180
  (Polychromatic418967fa.accept_7_2_3_5_1_34 23 143 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 143 180 (accept_3_4 22 143 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 143 180 (Polychromatic418967fa.accept_16_5_15_4_1_9099 21 143 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 143 180 (Polychromatic418967fa.accept_17_3_7_10_1_3948 20 143 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 143 180 (accept_3_4 19 143 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 143 180 (Polychromatic418967fa.accept_17_1_7_10_1_1835 18 143
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 143 180
  (Polychromatic418967fa.accept_22_17_11_4_1_10361 17 143 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 143 180 (accept_3_4 16 143 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 143 180 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 143 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 143 180 (Polychromatic418967fa.accept_16_14_15_4_1_3268 14 143
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 143 180 (accept_3_4 13 143
  180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 143 180
  (Polychromatic418967fa.accept_16_12_15_4_1_5422 12 143 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 143 180 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 143 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 143 180 (accept_3_4 10 143 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 143 180 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 143 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 143 180
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 143 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 143 180 (accept_3_4 7 143 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  143 180 (Polychromatic418967fa.accept_19_6_10_9_1_10215 6 143 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 143 180 (Polychromatic418967fa.accept_14_5_3_12_1_324 5 143 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 143 180 (accept_3_4 4 143 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 143 180 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 143 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 143 180
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 143 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 143 180 (accept_3_4 1 143 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 143
  180)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 142 180 (Eq.refl Bool.true) (allA_succ_of_gcd 38 142 180 2 19
  71 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 142 180
  (Polychromatic418967fa.accept_22_15_10_4_1_10294 37 142 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 142 180 2 18 71 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 142 180 (accept_3_5 35 142 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 142 180 2 17 71 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 142 180 (Polychromatic418967fa.accept_13_7_12_11_1_1911 33 142 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 142 180 2 16 71 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 142 180
  (Polychromatic418967fa.accept_7_3_2_5_1_147 31 142 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 142 180 2 15 71 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 142 180 (accept_3_5 29 142 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 142 180 2 14 71 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 142 180 (Polychromatic418967fa.accept_11_5_10_4_1_1157 27 142 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 142 180 2 13 71 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 142 180
  (Polychromatic418967fa.accept_7_4_2_5_1_527 25 142 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 142 180 2 12 71 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 142 180 (accept_3_5 23 142 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 142 180 2 11 71 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 142 180 (Polychromatic418967fa.accept_14_7_2_12_1_1430 21 142 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 142 180 2 10 71 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 142 180
  (Polychromatic418967fa.accept_25_19_17_5_1_10360 19 142 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 142 180 2 9 71 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 142 180 (accept_3_5 17 142 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 142 180 2 8 71 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 142 180 (Polychromatic418967fa.accept_16_15_14_4_1_6649 15 142 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 142 180 2 7 71 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 142 180
  (Polychromatic418967fa.accept_25_13_17_5_1_10359 13 142 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 142 180 2 6 71 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 142 180 (accept_3_5 11 142 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 142 180 2 5 71 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 142 180 (Polychromatic418967fa.accept_16_9_14_4_1_3225 9 142 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 142 180 2 4 71 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 142 180 (Polychromatic418967fa.accept_13_7_12_11_1_1911 7 142
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 142 180 2 3 71 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 142 180 (accept_3_5 5
  142 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 142 180 2 2 71 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 142 180
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 142 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 142 180 2 1 71 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 142 180 (Polychromatic418967fa.accept_13_1_12_11_1_728 1 142 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 142 180))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 141 180
  (Eq.refl Bool.true) (allA_succ_of_gcd 39 141 180 3 13 47 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 141 180 (Polychromatic418967fa.accept_7_3_1_5_1_44 38 141 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 141 180
  (Polychromatic418967fa.accept_19_18_8_9_1_3325 37 141 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 141 180 3 12 47 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 141 180 (Polychromatic418967fa.accept_11_2_9_4_1_310 35 141 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 141 180 (Polychromatic418967fa.accept_7_6_1_5_1_322
  34 141 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 141 180 3 11 47 60
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 141 180
  (Polychromatic418967fa.accept_7_4_1_5_1_540 32 141 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 141 180 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 141 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 141 180 3 10 47 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 141 180
  (Polychromatic418967fa.accept_17_12_5_10_1_5160 29 141 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 141 180 (Polychromatic418967fa.accept_16_12_13_4_1_3198 28 141 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 141 180 3 9 47 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 141 180
  (Polychromatic418967fa.accept_19_7_8_9_1_7322 26 141 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 141 180 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 141 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 141 180 3 8 47 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 141 180 (Polychromatic418967fa.accept_16_7_13_4_1_1348
  23 141 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 141 180
  (Polychromatic418967fa.accept_16_6_13_4_1_643 22 141 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 141 180 3 7 47 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 141 180 (Polychromatic418967fa.accept_7_6_1_5_1_322 20 141 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 141 180 (Polychromatic418967fa.accept_21_19_15_12_1_5523 19
  141 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 141 180 3 6 47 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 141 180
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 141 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 141 180 (Polychromatic418967fa.accept_19_16_8_9_1_8858 16 141 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 141 180 3 5 47 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 141 180
  (Polychromatic418967fa.accept_17_14_5_10_1_9052 14 141 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 141 180 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 141 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 141 180 3 4 47 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 141 180
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 141 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 141 180 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 141 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 141 180 3 3 47 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 141 180 (Polychromatic418967fa.accept_16_8_13_4_1_3258 8 141 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 180
  (Polychromatic418967fa.accept_16_7_13_4_1_1348 7 141 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 141 180 3 2 47 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 141 180 (Polychromatic418967fa.accept_21_5_15_12_1_5519 5 141 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 180 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 141 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 141 180 3 1 47 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 141 180
  (Polychromatic418967fa.accept_11_2_9_4_1_310 2 141 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 141 180 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 141 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 141 180)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 140 180
  (Eq.refl Bool.true) (allA_succ_of_gcd 40 140 180 20 2 7 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 140 180 (Polychromatic418967fa.accept_16_7_12_4_1_1347 39 140 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 140 180 2 19 70 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 140 180 (accept_3_4 37 140 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 140 180 4 9 35 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 140 180 5 7 28 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 140 180 2 17 70 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 140 180
  (Polychromatic418967fa.accept_16_1_12_4_1_695 33 140 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 140 180 4 8 35 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 140 180 (accept_3_4 31 140 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  140 180 10 3 14 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 140 180 (Polychromatic418967fa.accept_11_7_8_4_1_718 29 140 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 140 180 4 7 35 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 140 180
  (Polychromatic418967fa.accept_13_1_10_11_1_1280 27 140 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 140 180 2 13 70 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 25 140 180 5 5 28 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 140 180 4 6 35 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 140 180 (Polychromatic418967fa.accept_11_1_8_4_1_717 23 140 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 140 180 2 11 70 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 140 180
  (Polychromatic418967fa.accept_13_8_10_11_1_2730 21 140 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 140 180 20 1 7 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 140 180 (accept_3_4 19 140 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 140 180 2 9 70 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 140 180 (Polychromatic418967fa.accept_13_4_10_11_1_1908 17 140 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 140 180 4 4 35 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 140 180 5 3 28 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 140 180 2 7 70 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 140 180 (accept_3_4 13 140 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 140 180 4 3 35 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 140 180
  (Polychromatic418967fa.accept_16_11_12_4_1_3195 11 140 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 140 180 10 1 14 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 140 180 (Polychromatic418967fa.accept_16_9_12_4_1_3255 9 140 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 140 180 4 2 35 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 140 180 (accept_3_4 7 140 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 140 180 2 3 70 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 140 180 5 1 28 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 140 180 4 1 35 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 140 180 (Polychromatic418967fa.accept_13_3_10_11_1_1293 3 140
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 140 180 2 1 70 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 140 180 (accept_3_4 1
  140 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140 180)))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 42 139 180 (Eq.refl Bool.true) (allA_succ_of_accept 41 139 180 (accept_3_5 41 139 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 139 180 (Polychromatic418967fa.accept_13_1_9_11_1_703 40 139 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 139 180
  (Polychromatic418967fa.accept_7_4_6_5_1_141 39 139 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 139 180 (accept_3_5 38 139 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 139 180 (Polychromatic418967fa.accept_19_18_6_9_1_5991 37 139 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 139 180 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 139 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 139 180 (accept_3_5 35 139 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 139 180 (Polychromatic418967fa.accept_13_8_9_11_1_1265 34 139 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 139 180
  (Polychromatic418967fa.accept_13_7_9_11_1_705 33 139 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 139 180 (accept_3_5 32 139 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 139 180 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 139 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 139 180 (Polychromatic418967fa.accept_11_8_7_4_1_3011 30 139 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 139 180 (accept_3_5 29 139 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 139 180 (Polychromatic418967fa.accept_13_2_9_11_1_258 28 139
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 139 180
  (Polychromatic418967fa.accept_13_1_9_11_1_703 27 139 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 139 180 (accept_3_5 26 139 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 139 180 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 139 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 139 180 (Polychromatic418967fa.accept_16_8_11_4_1_3290 24 139 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 139 180 (accept_3_5 23 139 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 139 180 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 139 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 139 180
  (Polychromatic418967fa.accept_13_8_9_11_1_1265 21 139 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 139 180 (accept_3_5 20 139 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 139 180 (Polychromatic418967fa.accept_11_8_7_4_1_3011 19 139 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 139 180 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 139 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 139 180 (accept_3_5 17 139 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 139 180 (Polychromatic418967fa.accept_19_16_6_9_1_7335 16 139 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 139 180
  (Polychromatic418967fa.accept_7_1_6_5_1_39 15 139 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 139 180 (accept_3_5 14 139 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 139 180 (Polychromatic418967fa.accept_17_13_3_10_1_5157 13 139 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 139 180 (Polychromatic418967fa.accept_16_12_11_4_1_1359 12 139 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 139 180 (accept_3_5 11 139 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 139 180 (Polychromatic418967fa.accept_19_10_6_9_1_7312 10 139
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 139 180
  (Polychromatic418967fa.accept_16_9_11_4_1_3194 9 139 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 139 180 (accept_3_5 8 139 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  139 180 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 139 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 139 180 (Polychromatic418967fa.accept_14_6_13_12_1_810 6 139 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 139 180 (accept_3_5 5 139 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 139 180 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 139 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 139 180
  (Polychromatic418967fa.accept_11_3_7_4_1_1133 3 139 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 139 180 (accept_3_5 2 139 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  139 180 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 139 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 139 180)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 138 180 (Eq.refl Bool.true)
  (allA_succ_of_gcd 42 138 180 6 7 23 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 138 180 (Polychromatic418967fa.accept_24_17_18_12_1_1812 41 138 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 138 180 2 20 69 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 138 180 3 13 46 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 138 180 2 19 69 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 138 180
  (Polychromatic418967fa.accept_19_18_5_9_1_1112 37 138 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 138 180 6 6 23 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 138 180 (Polychromatic418967fa.accept_11_2_6_4_1_3028 35 138 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 138 180 2 17 69 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 138 180 3 11 46 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 138 180 2 16 69 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 138 180
  (Polychromatic418967fa.accept_19_12_5_9_1_7320 31 138 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 138 180 6 5 23 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 138 180 (Polychromatic418967fa.accept_13_3_8_11_1_1906 29 138 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 138 180 2 14 69 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 138 180 3 9 46 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 138 180 2 13 69 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 138 180
  (Polychromatic418967fa.accept_17_8_2_10_1_2879 25 138 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 138 180 6 4 23 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 138 180 (Polychromatic418967fa.accept_13_10_8_11_1_1985 23 138 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 138 180 2 11 69 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 138 180 3 7 46 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 138 180 2 10 69 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 138 180
  (Polychromatic418967fa.accept_13_6_8_11_1_5398 19 138 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 138 180 6 3 23 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 138 180 (Polychromatic418967fa.accept_13_4_8_11_1_1937 17 138 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 138 180 2 8 69 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 138 180 3 5 46 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 138 180 2 7 69 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 138 180 (Polychromatic418967fa.accept_11_2_6_4_1_3028
  13 138 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 138 180 6 2 23 30
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 138 180
  (Polychromatic418967fa.accept_22_11_6_4_1_5345 11 138 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 138 180 2 5 69 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 138 180 3 3 46 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 138 180 2 4 69 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 138 180 (Polychromatic418967fa.accept_19_7_5_9_1_10202 7 138 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 138 180 6 1 23 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 138 180 (Polychromatic418967fa.accept_22_5_6_4_1_10358 5 138 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 138 180 2 2 69 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 138 180 3 1 46 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 138 180 2 1 69 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 138 180
  (Polychromatic418967fa.accept_13_1_8_11_1_724 1 138 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 138 180))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 137 180 (Eq.refl Bool.true)
  (allA_succ_of_accept 43 137 180 (accept_3_4 43 137 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 137 180 (Polychromatic418967fa.accept_13_3_7_11_1_1904 42 137 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 137 180 (Polychromatic418967fa.accept_7_6_4_5_1_314 41 137 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 137 180 (accept_3_4 40 137 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 137 180 (Polychromatic418967fa.accept_21_18_11_12_1_7119 39 137 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 137 180
  (Polychromatic418967fa.accept_13_12_7_11_1_1935 38 137 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 137 180 (accept_3_4 37 137 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 137 180 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 137 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 137 180 (Polychromatic418967fa.accept_13_9_7_11_1_1292 35 137
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 137 180 (accept_3_4 34 137
  180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 137 180
  (Polychromatic418967fa.accept_19_14_4_9_1_6009 33 137 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 137 180 (Polychromatic418967fa.accept_11_10_5_4_1_711 32 137 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 137 180 (accept_3_4 31 137 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 137 180 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 137 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 137 180 (Polychromatic418967fa.accept_7_1_4_5_1_35 29
  137 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 137 180 (accept_3_4 28
  137 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 137 180
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 137 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 137 180 (Polychromatic418967fa.accept_17_9_1_10_1_2859 26 137 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 137 180 (accept_3_4 25 137 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 137 180 (Polychromatic418967fa.accept_16_8_9_4_1_630 24 137 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 137 180
  (Polychromatic418967fa.accept_7_2_4_5_1_313 23 137 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 137 180 (accept_3_4 22 137 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 137 180 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 137 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 137 180 (Polychromatic418967fa.accept_7_6_4_5_1_314 20 137 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 137 180 (accept_3_4 19 137 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 137 180 (Polychromatic418967fa.accept_13_5_7_11_1_3470 18 137 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 137 180
  (Polychromatic418967fa.accept_13_4_7_11_1_1981 17 137 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 137 180 (accept_3_4 16 137 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 137 180 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 137 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 137 180 (Polychromatic418967fa.accept_13_1_7_11_1_702 14 137 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 137 180 (accept_3_4 13 137 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 137 180 (Polychromatic418967fa.accept_13_12_7_11_1_1935 12 137
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 137 180
  (Polychromatic418967fa.accept_16_11_9_4_1_5438 11 137 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 137 180 (accept_3_4 10 137 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  137 180 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 137 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 137 180 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 137 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 137 180 (accept_3_4 7 137 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 137 180 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 137 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 137 180
  (Polychromatic418967fa.accept_8_5_1_4_1_628 5 137 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 137 180 (accept_3_4 4 137 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  137 180 (Polychromatic418967fa.accept_13_3_7_11_1_1904 3 137 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 137 180 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 137 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 137 180 (accept_3_4 1 137 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 137 180)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 136 180 (Eq.refl
  Bool.true) (allA_succ_of_gcd 44 136 180 4 11 34 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 136 180 (Polychromatic418967fa.accept_7_1_3_5_1_33 43 136 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 136 180 2 21 68 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 136 180 (accept_3_5 41 136 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 136 180 4 10 34 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 136 180
  (Polychromatic418967fa.accept_16_7_8_4_1_689 39 136 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 136 180 2 19 68 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 136 180 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 136 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 136 180 4 9 34 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 136 180 (accept_3_5 35 136 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 136 180 2 17 68 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 136 180
  (Polychromatic418967fa.accept_14_5_10_12_1_1454 33 136 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 136 180 4 8 34 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 136 180 (Polychromatic418967fa.accept_13_5_6_11_1_1933 31 136 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 136 180 2 15 68 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 136 180 (accept_3_5 29 136 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 136 180 4 7 34 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 136 180
  (Polychromatic418967fa.accept_16_11_8_4_1_2234 27 136 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 136 180 2 13 68 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 136 180 (Polychromatic418967fa.accept_16_9_8_4_1_1354 25 136 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 136 180 4 6 34 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 136 180 (accept_3_5 23 136 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 136 180 2 11 68 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 136 180
  (Polychromatic418967fa.accept_13_8_6_11_1_1979 21 136 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 136 180 4 5 34 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 136 180 (Polychromatic418967fa.accept_14_5_10_12_1_1454 19 136 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 136 180 2 9 68 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 136 180 (accept_3_5 17 136 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 136 180 4 4 34 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 136 180 (Polychromatic418967fa.accept_7_1_3_5_1_33 15
  136 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 136 180 2 7 68 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 136 180
  (Polychromatic418967fa.accept_16_13_8_4_1_3250 13 136 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 136 180 4 3 34 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 136 180 (accept_3_5 11 136 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  136 180 2 5 68 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 136 180 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 136 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 136 180 4 2 34 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 136 180 (Polychromatic418967fa.accept_16_7_8_4_1_689 7 136 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 136 180 2 3 68 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 136 180 (accept_3_5 5 136 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 136 180 4 1 34 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 136 180 (Polychromatic418967fa.accept_16_3_8_4_1_3279 3 136 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 136 180 2 1 68 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 136 180
  (Polychromatic418967fa.accept_7_1_3_5_1_33 1 136 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 136 180))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 135 180 (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 135 180 45 1 3 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 135 180 (Polychromatic418967fa.accept_16_12_7_4_1_687 44 135 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 135 180 (Polychromatic418967fa.accept_8_3_7_4_1_42 43 135 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 135 180 3 14 45 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 135 180
  (Polychromatic418967fa.accept_17_7_16_10_1_1849 41 135 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 135 180 5 8 27 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 39 135 180 3 13 45 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 135 180 (Polychromatic418967fa.accept_7_3_2_5_1_147 38 135 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 135 180
  (Polychromatic418967fa.accept_19_18_2_9_1_8870 37 135 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 135 180 9 4 15 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 135 180 5 7 27 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 135 180 (Polychromatic418967fa.accept_19_15_2_9_1_10357 34 135 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 135 180 3 11 45 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 135 180
  (Polychromatic418967fa.accept_7_4_2_5_1_527 32 135 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 135 180 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 135 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 135 180 15 2 9 12 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 135 180 (Polychromatic418967fa.accept_11_7_3_4_1_729
  29 135 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 135 180
  (Polychromatic418967fa.accept_16_12_7_4_1_687 28 135 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 135 180 9 3 15 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 135 180 (Polychromatic418967fa.accept_17_9_16_10_1_362 26 135 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 135 180 5 5 27 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 135 180 3 8 45 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 135 180
  (Polychromatic418967fa.accept_17_6_16_10_1_2890 23 135 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 135 180 (Polychromatic418967fa.accept_21_1_9_12_1_2719 22 135 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 135 180 3 7 45 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 135 180 5 4 27 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 135 180
  (Polychromatic418967fa.accept_8_3_7_4_1_42 19 135 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 135 180 9 2 15 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 135 180 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 135 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 135 180 (Polychromatic418967fa.accept_13_3_5_11_1_716 16 135
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 135 180 15 1 9 12 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 135 180
  (Polychromatic418967fa.accept_16_14_7_4_1_3243 14 135 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 135 180 (Polychromatic418967fa.accept_16_13_7_4_1_3248 13 135 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 135 180 3 4 45 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 135 180 (Polychromatic418967fa.accept_7_4_2_5_1_527 11
  135 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 135 180 5 2 27 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 135 180 9 1 15 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 135 180
  (Polychromatic418967fa.accept_16_8_7_4_1_2217 8 135 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 135 180 (Polychromatic418967fa.accept_11_7_3_4_1_729 7 135 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 135 180 3 2 45 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 135 180 5 1 27 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 135 180 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 135 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 135 180 3 1 45 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 135 180
  (Polychromatic418967fa.accept_21_2_9_12_1_4040 2 135 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 135 180 (Polychromatic418967fa.accept_19_1_2_9_1_3314 1 135 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 135 180)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 134 180
  (Eq.refl Bool.true) (allA_succ_of_gcd 46 134 180 2 23 67 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 134 180 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 134 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 134 180 2 22 67 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 134 180 (accept_3_4 43
  134 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 134 180 2 21 67 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 134 180
  (Polychromatic418967fa.accept_7_6_1_5_1_322 41 134 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 134 180 2 20 67 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 134 180 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 134 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 134 180 2 19 67 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 134 180 (accept_3_4 37 134 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 134 180 2 18 67 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 134 180 (Polychromatic418967fa.accept_16_3_6_4_1_679
  35 134 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 134 180 2 17 67 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 134 180
  (Polychromatic418967fa.accept_13_7_4_11_1_1967 33 134 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 134 180 2 16 67 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 134 180 (accept_3_4 31 134 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 134 180 2 15 67 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 134 180 (Polychromatic418967fa.accept_16_13_6_4_1_3277 29 134 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 134 180 2 14 67 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 134 180
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 134 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 134 180 2 13 67 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 134 180 (accept_3_4 25 134 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 134 180 2 12 67 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 134 180 (Polychromatic418967fa.accept_13_10_4_11_1_1969 23 134 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 134 180 2 11 67 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 134 180
  (Polychromatic418967fa.accept_13_8_4_11_1_3469 21 134 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 134 180 2 10 67 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 134 180 (accept_3_4 19 134 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 134 180 2 9 67 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 134 180 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 134 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 134 180 2 8 67 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 134 180 (Polychromatic418967fa.accept_13_2_4_11_1_2003
  15 134 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 134 180 2 7 67 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 134 180
  (accept_3_4 13 134 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 134 180 2 6 67 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 134 180
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 134 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 134 180 2 5 67 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 134 180 (Polychromatic418967fa.accept_11_9_2_4_1_707 9 134 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 134 180 2 4 67 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 134 180 (accept_3_4 7 134 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 134 180 2 3 67 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 134 180 (Polychromatic418967fa.accept_16_5_6_4_1_3211 5 134 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 134 180 2 2 67 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 134 180 (Polychromatic418967fa.accept_7_3_1_5_1_44 3
  134 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 134 180 2 1 67 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 134 180 (accept_3_4 1
  134 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134 180)))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 48 133 180 (Eq.refl Bool.true) (allA_succ_of_accept 47 133 180 (accept_3_5 47 133 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 133 180 (Polychromatic418967fa.accept_13_7_3_11_1_280 46 133 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 133 180
  (Polychromatic418967fa.accept_21_3_7_12_1_8725 45 133 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 133 180 (accept_3_5 44 133 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 133 180 (Polychromatic418967fa.accept_21_1_7_12_1_1465 43 133 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 133 180 (Polychromatic418967fa.accept_24_18_13_12_1_6679 42 133 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 133 180 (accept_3_5 41 133 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 133 180 (Polychromatic418967fa.accept_13_1_3_11_1_1289 40 133
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 133 180
  (Polychromatic418967fa.accept_17_5_14_10_1_2831 39 133 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 133 180 (accept_3_5 38 133 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 133 180 (Polychromatic418967fa.accept_14_9_7_12_1_4034 37 133 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 133 180 (Polychromatic418967fa.accept_13_10_3_11_1_1923 36 133
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 133 180 (accept_3_5 35 133
  180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 133 180
  (Polychromatic418967fa.accept_13_8_3_11_1_3467 34 133 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 133 180 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 133 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 133 180 (accept_3_5 32 133 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 133 180 (Polychromatic418967fa.accept_13_5_3_11_1_1288 31 133 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 133 180
  (Polychromatic418967fa.accept_11_8_1_4_1_2318 30 133 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 133 180 (accept_3_5 29 133 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 133 180 (Polychromatic418967fa.accept_13_2_3_11_1_1287 28 133 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 133 180 (Polychromatic418967fa.accept_13_1_3_11_1_1289 27 133 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 133 180 (accept_3_5 26 133 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 133 180 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 133 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 133 180
  (Polychromatic418967fa.accept_16_8_5_4_1_674 24 133 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 133 180 (accept_3_5 23 133 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 133 180 (Polychromatic418967fa.accept_16_6_5_4_1_4330 22 133 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 133 180 (Polychromatic418967fa.accept_13_8_3_11_1_3467 21 133 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 133 180 (accept_3_5 20 133 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 133 180 (Polychromatic418967fa.accept_11_8_1_4_1_2318 19 133
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 133 180
  (Polychromatic418967fa.accept_13_5_3_11_1_1288 18 133 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 133 180 (accept_3_5 17 133 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 133 180 (Polychromatic418967fa.accept_14_2_7_12_1_1485 16 133 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 133 180 (Polychromatic418967fa.accept_13_2_3_11_1_1287 15 133 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 133 180 (accept_3_5 14 133 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 133 180 (Polychromatic418967fa.accept_17_13_14_10_1_1847 13
  133 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 133 180
  (Polychromatic418967fa.accept_16_12_5_4_1_3275 12 133 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 133 180 (accept_3_5 11 133 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 133 180 (Polychromatic418967fa.accept_13_10_3_11_1_1923 10 133 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 133 180 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 133 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 133 180 (accept_3_5 8 133 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 133 180 (Polychromatic418967fa.accept_13_7_3_11_1_280 7 133 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 133 180
  (Polychromatic418967fa.accept_16_6_5_4_1_4330 6 133 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 133 180 (accept_3_5 5 133 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  133 180 (Polychromatic418967fa.accept_21_4_7_12_1_10320 4 133 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 133 180 (Polychromatic418967fa.accept_21_3_7_12_1_8725 3 133 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 133 180 (accept_3_5 2 133 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 133 180 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 133 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 133
  180)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 132 180 (Eq.refl Bool.true) (allA_succ_of_gcd 48
  132 180 12 4 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 132 180 (Polychromatic418967fa.accept_21_5_6_12_1_7091 47 132 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 132 180 2 23 66 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 132 180 3 15 44 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 132 180 4 11 33 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 132 180
  (Polychromatic418967fa.accept_7_1_6_5_1_39 43 132 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 132 180 6 7 22 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 132 180 (Polychromatic418967fa.accept_14_13_6_12_1_3126 41 132 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 132 180 4 10 33 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 132 180 3 13 44 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 132 180 2 19 66 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 132 180
  (Polychromatic418967fa.accept_17_3_13_10_1_3935 37 132 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 132 180 12 3 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 132 180 (Polychromatic418967fa.accept_13_9_2_11_1_1964 35 132 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 132 180 2 17 66 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 132 180 3 11 44 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 132 180 4 8 33 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 132 180
  (Polychromatic418967fa.accept_17_14_13_10_1_3936 31 132 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 132 180 6 5 22 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 132 180 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 132 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 132 180 4 7 33 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 132 180 3 9 44 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 132 180 2 13 66 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 132 180
  (Polychromatic418967fa.accept_7_4_6_5_1_141 25 132 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 132 180 12 2 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 132 180 (Polychromatic418967fa.accept_13_10_2_11_1_1920 23 132 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 132 180 2 11 66 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 132 180 3 7 44 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 132 180 4 5 33 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 132 180
  (Polychromatic418967fa.accept_21_19_6_12_1_7089 19 132 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 132 180 6 3 22 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 132 180 (Polychromatic418967fa.accept_13_4_2_11_1_733 17 132 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 132 180 4 4 33 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 132 180 3 5 44 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 132 180 2 7 66 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 132 180
  (Polychromatic418967fa.accept_14_13_6_12_1_3126 13 132 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 132 180 12 1 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 132 180 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 132 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 132 180 2 5 66 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 132 180 3 3 44 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 132 180 4 2 33 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 132 180
  (Polychromatic418967fa.accept_21_7_6_12_1_10316 7 132 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 132 180 6 1 22 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 132 180 (Polychromatic418967fa.accept_17_5_13_10_1_3949 5 132 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 132 180 4 1 33 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 132 180 3 1 44 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 132 180 2 1 66 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 132 180 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 132 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132
  180))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 131 180 (Eq.refl Bool.true) (allA_succ_of_accept
  49 131 180 (accept_3_4 49 131 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 131 180
  (Polychromatic418967fa.accept_13_9_1_11_1_275 48 131 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 131 180 (Polychromatic418967fa.accept_8_7_3_4_1_404 47 131 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 131 180 (accept_3_4 46 131 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 131 180 (Polychromatic418967fa.accept_14_3_5_12_1_4000 45 131 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 131 180
  (Polychromatic418967fa.accept_16_12_3_4_1_4317 44 131 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 131 180 (accept_3_4 43 131 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 131 180 (Polychromatic418967fa.accept_13_3_1_11_1_1268 42 131 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 131 180 (Polychromatic418967fa.accept_27_14_23_18_1_10356 41 131 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 131 180 (accept_3_4 40 131 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 131 180 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 131 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 131 180
  (Polychromatic418967fa.accept_11_5_10_4_1_1157 38 131 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 131 180 (accept_3_4 37 131 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 131 180 (Polychromatic418967fa.accept_13_10_1_11_1_1961 36 131 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 131 180 (Polychromatic418967fa.accept_13_9_1_11_1_275 35 131 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 131 180 (accept_3_4 34 131 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 131 180 (Polychromatic418967fa.accept_13_7_1_11_1_732 33 131
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 131 180
  (Polychromatic418967fa.accept_19_13_17_9_1_3312 32 131 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 131 180 (accept_3_4 31 131 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 131 180 (Polychromatic418967fa.accept_19_11_17_9_1_10138 30 131 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 131 180
  (Polychromatic418967fa.accept_13_3_1_11_1_1268 29 131 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 131 180 (accept_3_4 28 131 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 131 180 (Polychromatic418967fa.accept_11_5_10_4_1_1157 27 131 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 131 180 (Polychromatic418967fa.accept_19_7_17_9_1_8879 26 131 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 131 180 (accept_3_4 25 131 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 131 180 (Polychromatic418967fa.accept_14_10_5_12_1_3995 24 131
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 131 180
  (Polychromatic418967fa.accept_8_7_3_4_1_404 23 131 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 131 180 (accept_3_4 22 131 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 131 180 (Polychromatic418967fa.accept_13_8_1_11_1_1284 21 131 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 131 180 (Polychromatic418967fa.accept_13_7_1_11_1_732 20 131 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 131 180 (accept_3_4 19 131 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 131 180 (Polychromatic418967fa.accept_21_18_5_12_1_4032 18 131
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 131 180
  (Polychromatic418967fa.accept_14_3_5_12_1_4000 17 131 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 131 180 (accept_3_4 16 131 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 131 180 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 131 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 131 180 (Polychromatic418967fa.accept_19_14_17_9_1_5959 14 131 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 131 180 (accept_3_4 13 131 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 131 180 (Polychromatic418967fa.accept_13_12_1_11_1_1917 12 131
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 131 180
  (Polychromatic418967fa.accept_19_11_17_9_1_10138 11 131 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 131 180 (accept_3_4 10 131 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 131 180 (Polychromatic418967fa.accept_13_9_1_11_1_275 9 131 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 131 180 (Polychromatic418967fa.accept_13_8_1_11_1_1284 8 131
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 131 180 (accept_3_4 7 131 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 131 180 (Polychromatic418967fa.accept_16_6_3_4_1_6624
  6 131 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 131 180
  (Polychromatic418967fa.accept_11_5_10_4_1_1157 5 131 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 131 180 (accept_3_4 4 131 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  131 180 (Polychromatic418967fa.accept_13_3_1_11_1_1268 3 131 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 131 180 (Polychromatic418967fa.accept_17_2_12_10_1_9034 2 131 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 131 180 (accept_3_4 1 131 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 131 180)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 130
  180 (Eq.refl Bool.true) (allA_succ_of_gcd 50 130 180 10 5 13 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 130 180 (Polychromatic418967fa.accept_21_7_4_12_1_8684 49 130
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 130 180 2 24 65 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 130 180 (accept_3_5 47
  130 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 130 180 2 23 65 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 130 180 5 9 26 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 130 180 2 22 65 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 130 180
  (Polychromatic418967fa.accept_7_1_4_5_1_35 43 130 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 130 180 2 21 65 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 130 180 (accept_3_5 41 130 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 130 180 10 4 13 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 130 180 (Polychromatic418967fa.accept_21_18_4_12_1_4068 39 130 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 130 180 2 19 65 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 130 180
  (Polychromatic418967fa.accept_7_2_4_5_1_313 37 130 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 130 180 2 18 65 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 35 130 180 5 7 26 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 34 130 180 2 17 65 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 130 180 (Polychromatic418967fa.accept_19_14_16_9_1_8834 33 130 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 130 180 2 16 65 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 130 180
  (Polychromatic418967fa.accept_19_12_16_9_1_5976 31 130 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 130 180 10 3 13 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 130 180 (accept_3_5 29 130 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 130 180 2 14 65 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 130 180 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 130 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 130 180 2 13 65 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 130 180 5 5 26 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 130 180 2 12 65 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 130 180 (accept_3_5 23 130 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 130 180 2 11 65 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 130 180
  (Polychromatic418967fa.accept_17_4_11_10_1_5167 21 130 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 130 180 10 2 13 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 130 180 (Polychromatic418967fa.accept_21_19_4_12_1_4027 19 130 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 130 180 2 9 65 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 130 180 (accept_3_5 17
  130 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 130 180 2 8 65 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 130 180 5 3 26 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 130 180 2 7 65 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 130 180
  (Polychromatic418967fa.accept_7_6_4_5_1_314 13 130 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 130 180 2 6 65 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 130 180 (accept_3_5 11 130 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  130 180 10 1 13 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 130 180 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 130 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 130 180 2 4 65 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 130 180 (Polychromatic418967fa.accept_19_7_16_9_1_398 7 130 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 130 180 2 3 65 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 130 180 5 1 26 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 130 180 2 2 65 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 130 180
  (Polychromatic418967fa.accept_17_3_11_10_1_7787 3 130 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 130 180 2 1 65 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 130 180 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 130 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 130 180))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52
  129 180 (Eq.refl Bool.true) (allA_succ_of_gcd 51 129 180 3 17 43 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 129 180 (Polychromatic418967fa.accept_7_1_3_5_1_33 50 129 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 129 180
  (Polychromatic418967fa.accept_13_10_12_11_1_731 49 129 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 129 180 3 16 43 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 129 180 (Polychromatic418967fa.accept_14_5_3_12_1_324 47 129 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 129 180
  (Polychromatic418967fa.accept_13_7_12_11_1_1911 46 129 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 129 180 3 15 43 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 129 180 (Polychromatic418967fa.accept_7_2_3_5_1_34 44 129 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 129 180
  (Polychromatic418967fa.accept_7_1_3_5_1_33 43 129 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 129 180 3 14 43 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 129 180 (Polychromatic418967fa.accept_19_3_15_9_1_4576 41 129 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 129 180
  (Polychromatic418967fa.accept_11_7_8_4_1_718 40 129 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 129 180 3 13 43 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 129 180 (Polychromatic418967fa.accept_21_17_3_12_1_3986 38 129 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 129 180
  (Polychromatic418967fa.accept_7_2_3_5_1_34 37 129 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 129 180 3 12 43 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 129 180 (Polychromatic418967fa.accept_16_3_1_4_1_5426 35 129 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 129 180
  (Polychromatic418967fa.accept_11_1_8_4_1_717 34 129 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 129 180 3 11 43 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 129 180 (Polychromatic418967fa.accept_19_13_15_9_1_3293 32 129 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 129 180
  (Polychromatic418967fa.accept_21_10_3_12_1_10214 31 129 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 129 180 3 10 43 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 129 180 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 129 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 129 180
  (Polychromatic418967fa.accept_16_12_1_4_1_5403 28 129 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 129 180 3 9 43 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 129 180 (Polychromatic418967fa.accept_25_1_4_5_1_10355 26 129 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 180 (Polychromatic418967fa.accept_19_6_15_9_1_10277 25 129
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 129 180 3 8 43 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 129 180
  (Polychromatic418967fa.accept_7_2_3_5_1_34 23 129 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 129 180 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 129 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 129 180 3 7 43 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 129 180
  (Polychromatic418967fa.accept_13_7_12_11_1_1911 20 129 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 129 180 (Polychromatic418967fa.accept_14_5_3_12_1_324 19 129 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 129 180 3 6 43 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 129 180
  (Polychromatic418967fa.accept_13_4_12_11_1_5362 17 129 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 129 180 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 129 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 129 180 3 5 43 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 129 180
  (Polychromatic418967fa.accept_13_1_12_11_1_728 14 129 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 129 180 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 129 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 129 180 3 4 43 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 129 180
  (Polychromatic418967fa.accept_19_11_15_9_1_6002 11 129 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 129 180 (Polychromatic418967fa.accept_13_10_12_11_1_731 10 129 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 129 180 3 3 43 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 129 180
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 129 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 129 180 (Polychromatic418967fa.accept_11_7_8_4_1_718 7 129 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 129 180 3 2 43 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 129 180 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 129 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 180
  (Polychromatic418967fa.accept_13_4_12_11_1_5362 4 129 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 129 180 3 1 43 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 129 180 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 129 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 180 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 129 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129
  180)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 128 180 (Eq.refl Bool.true) (allA_succ_of_gcd
  52 128 180 4 13 32 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 128 180 (Polychromatic418967fa.accept_21_9_2_12_1_10144 51 128 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 128 180 2 25 64 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 128 180 (accept_3_4 49 128 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 128 180 4 12 32 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 128 180 (Polychromatic418967fa.accept_11_3_7_4_1_1133
  47 128 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 128 180 2 23 64 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 128 180
  (Polychromatic418967fa.accept_7_3_2_5_1_147 45 128 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 128 180 4 11 32 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 128 180 (accept_3_4 43 128 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 128 180 2 21 64 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 128 180 (Polychromatic418967fa.accept_11_8_7_4_1_3011 41 128 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 128 180 4 10 32 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 128 180
  (Polychromatic418967fa.accept_7_4_2_5_1_527 39 128 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 128 180 2 19 64 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 128 180 (accept_3_4 37 128 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 128 180 4 9 32 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 128 180 (Polychromatic418967fa.accept_14_7_2_12_1_1430 35 128 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 128 180 2 17 64 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 128 180
  (Polychromatic418967fa.accept_17_16_9_10_1_3962 33 128 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 128 180 4 8 32 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 128 180 (accept_3_4 31 128 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 128 180 2 15 64 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 128 180 (Polychromatic418967fa.accept_23_6_13_19_1_10304 29 128 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 128 180 4 7 32 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 128 180
  (Polychromatic418967fa.accept_19_8_14_9_1_4590 27 128 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 128 180 2 13 64 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 128 180 (accept_3_4 25 128 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 128 180 4 6 32 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 128 180 (Polychromatic418967fa.accept_19_4_14_9_1_10227 23 128 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 128 180 2 11 64 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 128 180
  (Polychromatic418967fa.accept_14_7_2_12_1_1430 21 128 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 128 180 4 5 32 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 128 180 (accept_3_4 19 128 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  128 180 2 9 64 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  17 128 180 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 128 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 128 180 4 4 32 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 128 180 (Polychromatic418967fa.accept_28_15_16_12_1_10354 15 128 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 128 180 2 7 64 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 128 180 (accept_3_4 13
  128 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 128 180 4 3 32 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 128 180
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 128 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 128 180 2 5 64 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 128 180 (Polychromatic418967fa.accept_21_9_2_12_1_10144 9 128 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 128 180 4 2 32 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 128 180 (accept_3_4 7 128 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 128 180 2 3 64 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 128 180 (Polychromatic418967fa.accept_19_5_14_9_1_4554 5 128 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 128 180 4 1 32 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 128 180 (Polychromatic418967fa.accept_7_3_2_5_1_147 3
  128 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 128 180 2 1 64 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 128 180 (accept_3_4 1
  128 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128
  180))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 127 180 (Eq.refl Bool.true)
  (allA_succ_of_accept 53 127 180 (accept_3_5 53 127 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 127 180 (Polychromatic418967fa.accept_7_3_1_5_1_44 52 127 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 127 180 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 127 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 127 180 (accept_3_5 50 127 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 127 180 (Polychromatic418967fa.accept_17_15_8_10_1_2886 49 127 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 127 180
  (Polychromatic418967fa.accept_7_6_1_5_1_322 48 127 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 127 180 (accept_3_5 47 127 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 127 180 (Polychromatic418967fa.accept_7_4_1_5_1_540 46 127 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 127 180 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 127 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 127 180 (accept_3_5 44 127 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 127 180 (Polychromatic418967fa.accept_8_3_7_4_1_42 43 127 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 127 180
  (Polychromatic418967fa.accept_13_3_10_11_1_1293 42 127 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 127 180 (accept_3_5 41 127 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 127 180 (Polychromatic418967fa.accept_13_1_10_11_1_1280 40 127 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 127 180 (Polychromatic418967fa.accept_7_4_1_5_1_540
  39 127 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 127 180 (accept_3_5 38
  127 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 127 180
  (Polychromatic418967fa.accept_16_5_15_4_1_9099 37 127 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 127 180 (Polychromatic418967fa.accept_17_2_8_10_1_2870 36 127 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 127 180 (accept_3_5 35 127 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 127 180 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 127 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 127 180
  (Polychromatic418967fa.accept_22_11_17_4_1_10254 33 127 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 127 180 (accept_3_5 32 127 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 127 180 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 127 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 127 180 (Polychromatic418967fa.accept_13_4_10_11_1_1908 30 127
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 127 180 (accept_3_5 29 127
  180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 127 180
  (Polychromatic418967fa.accept_13_2_10_11_1_1276 28 127 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 127 180 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 127 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 127 180 (accept_3_5 26 127 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 127 180 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 127 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 127 180
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 127 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 127 180 (accept_3_5 23 127 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 127 180 (Polychromatic418967fa.accept_19_3_13_9_1_8876 22 127 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 127 180 (Polychromatic418967fa.accept_13_8_10_11_1_2730 21 127 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 127 180 (accept_3_5 20 127 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 127 180 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 127 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 127 180
  (Polychromatic418967fa.accept_7_4_1_5_1_540 18 127 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 127 180 (accept_3_5 17 127 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 127 180 (Polychromatic418967fa.accept_13_3_10_11_1_1293 16 127 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 127 180 (Polychromatic418967fa.accept_13_2_10_11_1_1276 15 127 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 127 180 (accept_3_5 14 127 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 127 180 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 127 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 127 180
  (Polychromatic418967fa.accept_13_12_10_11_1_1279 12 127 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 127 180 (accept_3_5 11 127 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 127 180 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 127 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 127 180 (Polychromatic418967fa.accept_21_9_1_12_1_3984 9 127
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 127 180 (accept_3_5 8 127 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 127 180
  (Polychromatic418967fa.accept_19_7_13_9_1_10179 7 127 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 127 180 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 127 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 127 180 (accept_3_5 5 127 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 127 180 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 127 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 127 180 (Polychromatic418967fa.accept_7_3_1_5_1_44 3
  127 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 127 180 (accept_3_5 2 127
  180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 127 180
  (Polychromatic418967fa.accept_13_1_10_11_1_1280 1 127 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 127 180)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 126 180 (Eq.refl Bool.true)
  (allA_succ_of_gcd 54 126 180 18 3 7 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 126 180 (Polychromatic418967fa.accept_13_1_9_11_1_703 53 126 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 126 180 2 26 63 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 126 180 3 17 42 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 126 180 2 25 63 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 126 180
  (Polychromatic418967fa.accept_16_1_14_4_1_3220 49 126 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 126 180 6 8 21 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 126 180 (Polychromatic418967fa.accept_13_8_9_11_1_1265 47 126 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 126 180 2 23 63 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 126 180 9 5 14 20 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 126 180 2 22 63 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 126 180
  (Polychromatic418967fa.accept_11_10_5_4_1_711 43 126 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 126 180 6 7 21 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 126 180 (Polychromatic418967fa.accept_13_2_9_11_1_258 41 126 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 126 180 2 20 63 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 126 180 3 13 42 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 126 180 2 19 63 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 126 180
  (Polychromatic418967fa.accept_17_3_7_10_1_3948 37 126 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 126 180 18 2 7 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 126 180 (Polychromatic418967fa.accept_17_1_7_10_1_1835 35 126 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 126 180 2 17 63 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 126 180 3 11 42 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 126 180 2 16 63 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 126 180
  (Polychromatic418967fa.accept_16_15_14_4_1_6649 31 126 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 126 180 6 5 21 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 126 180 (Polychromatic418967fa.accept_19_10_12_9_1_10150 29 126 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 126 180 2 14 63 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 126 180 9 3 14 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 126 180 2 13 63 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 126 180
  (Polychromatic418967fa.accept_16_9_14_4_1_3225 25 126 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 126 180 6 4 21 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 126 180 (Polychromatic418967fa.accept_16_7_14_4_1_1362 23 126 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 126 180 2 11 63 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 126 180 3 7 42 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 126 180 2 10 63 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 126 180
  (Polychromatic418967fa.accept_22_19_16_4_1_10248 19 126 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 126 180 18 1 7 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 126 180 (Polychromatic418967fa.accept_16_1_14_4_1_3220 17 126 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 126 180 2 8 63 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 126 180 3 5 42 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 126 180 2 7 63 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 126 180
  (Polychromatic418967fa.accept_24_13_6_12_1_10353 13 126 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 126 180 6 2 21 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 126 180 (Polychromatic418967fa.accept_22_11_16_4_1_10352 11 126 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 126 180 2 5 63 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 126 180 9 1 14 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 126 180 2 4 63 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 126 180
  (Polychromatic418967fa.accept_13_7_9_11_1_705 7 126 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 126 180 6 1 21 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 126 180 (Polychromatic418967fa.accept_19_5_12_9_1_4588 5 126 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 126 180 2 2 63 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 126 180 3 1 42 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 126 180 2 1 63 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 126 180 (Polychromatic418967fa.accept_13_1_9_11_1_703 1 126 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  180))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 125 180 (Eq.refl Bool.true)
  (allA_succ_of_gcd 55 125 180 5 11 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 54 125 180 (Polychromatic418967fa.accept_16_6_13_4_1_643 54 125 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 125 180
  (Polychromatic418967fa.accept_7_4_6_5_1_141 53 125 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 125 180 (accept_3_4 52 125 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 125 180 (Polychromatic418967fa.accept_21_9_20_12_1_5564 51 125 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 125 180 5 10 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 125 180 (accept_3_4 49 125 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 125 180 (Polychromatic418967fa.accept_13_9_8_11_1_725 48 125 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 125 180 (Polychromatic418967fa.accept_22_3_15_4_1_10351 47 125
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 125 180 (accept_3_4 46 125
  180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 125 180 5 9 25 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 125 180
  (Polychromatic418967fa.accept_16_12_13_4_1_3198 44 125 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 125 180 (accept_3_4 43 125 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 125 180 (Polychromatic418967fa.accept_13_3_8_11_1_1906 42 125 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 125 180 (Polychromatic418967fa.accept_8_1_5_4_1_388 41 125 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 125 180 5 8 25 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 125 180
  (Polychromatic418967fa.accept_7_4_6_5_1_141 39 125 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 125 180 (Polychromatic418967fa.accept_16_6_13_4_1_643 38 125 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 125 180 (accept_3_4 37 125 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 125 180 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 125 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 125 180 5 7 25 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 125 180 (accept_3_4 34 125 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 125 180 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 125 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 125 180
  (Polychromatic418967fa.accept_7_4_6_5_1_141 32 125 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 125 180 (accept_3_4 31 125 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  125 180 5 6 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 125 180 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 125 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 125 180 (accept_3_4 28 125 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 125 180 (Polychromatic418967fa.accept_13_1_8_11_1_724 27 125 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 125 180 (Polychromatic418967fa.accept_19_7_11_9_1_2139 26 125
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 125 180 5 5 25 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 125 180
  (Polychromatic418967fa.accept_16_8_13_4_1_3258 24 125 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 125 180 (Polychromatic418967fa.accept_13_10_8_11_1_1985 23 125 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 125 180 (accept_3_4 22 125 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 125 180 (Polychromatic418967fa.accept_17_4_6_10_1_5164 21 125 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 125 180 5 4 25 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 125 180 (accept_3_4 19
  125 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 125 180
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 125 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 125 180 (Polychromatic418967fa.accept_8_1_5_4_1_388 17 125 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 125 180 (accept_3_4 16 125 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 125 180 5 3 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 125 180 (Polychromatic418967fa.accept_13_1_8_11_1_724 14 125 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 125 180 (accept_3_4 13 125 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 125 180 (Polychromatic418967fa.accept_16_12_13_4_1_3198 12 125
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 125 180
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 125 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 125 180 5 2 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 125 180 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 125 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 125 180 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 125 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 125 180 (accept_3_4 7 125 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 125 180 (Polychromatic418967fa.accept_13_6_8_11_1_5398
  6 125 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 125 180 5 1 25 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 125 180 (accept_3_4 4
  125 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 125 180
  (Polychromatic418967fa.accept_13_3_8_11_1_1906 3 125 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 125 180 (Polychromatic418967fa.accept_19_2_11_9_1_1119 2 125 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 125 180 (accept_3_4 1 125 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 125 180)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 124 180 (Eq.refl
  Bool.true) (allA_succ_of_gcd 56 124 180 4 14 31 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 124 180 (Polychromatic418967fa.accept_13_3_7_11_1_1904 55 124 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 124 180 2 27 62 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 124 180 (accept_3_5 53 124 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 124 180 4 13 31 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 124 180
  (Polychromatic418967fa.accept_11_7_3_4_1_729 51 124 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 124 180 2 25 62 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 124 180 (Polychromatic418967fa.accept_16_1_12_4_1_695 49 124 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 124 180 4 12 31 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 124 180 (accept_3_5 47 124 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 124 180 2 23 62 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 124 180
  (Polychromatic418967fa.accept_16_13_12_4_1_4323 45 124 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 124 180 4 11 31 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 124 180 (Polychromatic418967fa.accept_13_4_7_11_1_1981 43 124 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 124 180 2 21 62 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 124 180 (accept_3_5 41 124 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 124 180 4 10 31 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 124 180
  (Polychromatic418967fa.accept_16_7_12_4_1_1347 39 124 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 124 180 2 19 62 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 124 180 (Polychromatic418967fa.accept_16_5_12_4_1_4325 37 124 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 124 180 4 9 31 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 124 180 (accept_3_5 35 124 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 124 180 2 17 62 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 124 180
  (Polychromatic418967fa.accept_16_1_12_4_1_695 33 124 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 124 180 4 8 31 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 124 180 (Polychromatic418967fa.accept_13_5_7_11_1_3470 31 124 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 124 180 2 15 62 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 124 180 (accept_3_5 29 124 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 124 180 4 7 31 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 124 180 (Polychromatic418967fa.accept_13_1_7_11_1_702 27 124
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 124 180 2 13 62 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 124 180
  (Polychromatic418967fa.accept_13_12_7_11_1_1935 25 124 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 124 180 4 6 31 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 124 180 (accept_3_5 23 124 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 124 180 2 11 62 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 124 180 (Polychromatic418967fa.accept_16_5_12_4_1_4325 21 124 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 124 180 4 5 31 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 124 180
  (Polychromatic418967fa.accept_16_3_12_4_1_170 19 124 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 124 180 2 9 62 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 124 180 (accept_3_5 17 124 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  124 180 4 4 31 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 124 180 (Polychromatic418967fa.accept_16_15_12_4_1_4324 15 124 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 124 180 2 7 62 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 124 180 (Polychromatic418967fa.accept_16_13_12_4_1_4323 13 124 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 124 180 4 3 31 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 124 180 (accept_3_5 11
  124 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 124 180 2 5 62 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 124 180
  (Polychromatic418967fa.accept_13_9_7_11_1_1292 9 124 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 124 180 4 2 31 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 124 180 (Polychromatic418967fa.accept_11_7_3_4_1_729 7 124 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 124 180 2 3 62 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 124 180 (accept_3_5 5 124 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 124 180 4 1 31 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 124 180 (Polychromatic418967fa.accept_13_3_7_11_1_1904 3 124 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 124 180 2 1 62 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 124 180 (Polychromatic418967fa.accept_13_1_7_11_1_702 1
  124 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 124
  180))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 123 180 (Eq.refl Bool.true)
  (allA_succ_of_gcd 57 123 180 3 19 41 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 123 180 (Polychromatic418967fa.accept_13_4_6_11_1_2017 56 123 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 123 180
  (Polychromatic418967fa.accept_7_6_4_5_1_314 55 123 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 123 180 3 18 41 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 123 180 (Polychromatic418967fa.accept_11_9_2_4_1_707 53 123 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 123 180
  (Polychromatic418967fa.accept_27_25_15_18_1_10280 52 123 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 51 123 180 3 17 41 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 50 123 180 (Polychromatic418967fa.accept_7_1_4_5_1_35 50 123 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 123 180
  (Polychromatic418967fa.accept_17_15_4_10_1_3968 49 123 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 123 180 3 16 41 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 123 180 (Polychromatic418967fa.accept_8_7_3_4_1_404 47 123 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 123 180
  (Polychromatic418967fa.accept_21_4_18_12_1_5532 46 123 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 123 180 3 15 41 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 123 180 (Polychromatic418967fa.accept_7_2_4_5_1_313 44 123 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 123 180
  (Polychromatic418967fa.accept_7_1_4_5_1_35 43 123 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 123 180 3 14 41 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 123 180 (Polychromatic418967fa.accept_7_6_4_5_1_314 41 123 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 123 180
  (Polychromatic418967fa.accept_16_8_11_4_1_3290 40 123 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 123 180 3 13 41 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 123 180 (Polychromatic418967fa.accept_16_6_11_4_1_635 38 123 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 123 180
  (Polychromatic418967fa.accept_7_2_4_5_1_313 37 123 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 123 180 3 12 41 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 123 180 (Polychromatic418967fa.accept_21_14_18_12_1_10349 35 123 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 123 180
  (Polychromatic418967fa.accept_7_6_4_5_1_314 34 123 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 123 180 3 11 41 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 123 180 (Polychromatic418967fa.accept_17_15_4_10_1_3968 32 123 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 180
  (Polychromatic418967fa.accept_8_7_3_4_1_404 31 123 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 123 180 3 10 41 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 123 180 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 123 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 123 180 (Polychromatic418967fa.accept_11_6_2_4_1_1703
  28 123 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 123 180 3 9 41 60
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 123 180
  (Polychromatic418967fa.accept_21_5_18_12_1_5531 26 123 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 123 180 (Polychromatic418967fa.accept_16_9_11_4_1_3194 25 123 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 123 180 3 8 41 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 123 180
  (Polychromatic418967fa.accept_7_2_4_5_1_313 23 123 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 123 180 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 123 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 123 180 3 7 41 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 123 180 (Polychromatic418967fa.accept_7_6_4_5_1_314 20
  123 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 180
  (Polychromatic418967fa.accept_21_19_18_12_1_10350 19 123 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 123 180 3 6 41 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 123 180 (Polychromatic418967fa.accept_11_6_2_4_1_1703 17 123 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 123 180
  (Polychromatic418967fa.accept_7_2_4_5_1_313 16 123 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 123 180 3 5 41 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 123 180 (Polychromatic418967fa.accept_21_14_18_12_1_10349 14 123 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 180 (Polychromatic418967fa.accept_7_6_4_5_1_314
  13 123 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 123 180 3 4 41 60
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 123 180
  (Polychromatic418967fa.accept_17_11_4_10_1_6430 11 123 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 123 180 (Polychromatic418967fa.accept_25_10_23_5_1_6517 10 123 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 123 180 3 3 41 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 123 180
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 123 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 123 180 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 123 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 123 180 3 2 41 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 123 180 (Polychromatic418967fa.accept_13_5_6_11_1_1933 5 123 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 180
  (Polychromatic418967fa.accept_13_4_6_11_1_2017 4 123 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 123 180 3 1 41 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 123 180 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 123 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 180 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 123 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 123
  180)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 122 180 (Eq.refl Bool.true)
  (allA_succ_of_gcd 58 122 180 2 29 61 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 122 180 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 122 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 122 180 2 28 61 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 122 180 (accept_3_4 55 122 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 122 180 2 27 61 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 122 180
  (Polychromatic418967fa.accept_27_26_14_18_1_10164 53 122 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 122 180 2 26 61 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 122 180 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 122 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 122 180 2 25 61 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 122 180 (accept_3_4 49 122 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 122 180 2 24 61 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 122 180
  (Polychromatic418967fa.accept_14_5_10_12_1_1454 47 122 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 122 180 2 23 61 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 122 180 (Polychromatic418967fa.accept_13_6_5_11_1_1971 45 122 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 122 180 2 22 61 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 122 180 (accept_3_4 43 122 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 122 180 2 21 61 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 122 180
  (Polychromatic418967fa.accept_11_8_1_4_1_2318 41 122 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 122 180 2 20 61 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 122 180 (Polychromatic418967fa.accept_19_1_8_9_1_3304 39 122 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 122 180 2 19 61 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 122 180 (accept_3_4 37 122 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 122 180 2 18 61 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 122 180
  (Polychromatic418967fa.accept_19_16_8_9_1_8858 35 122 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 122 180 2 17 61 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 122 180 (Polychromatic418967fa.accept_13_7_5_11_1_1927 33 122 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 122 180 2 16 61 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 122 180 (accept_3_4 31 122 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 122 180 2 15 61 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 122 180
  (Polychromatic418967fa.accept_7_1_3_5_1_33 29 122 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 122 180 2 14 61 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 122 180 (Polychromatic418967fa.accept_21_6_17_12_1_10348 27 122 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 122 180 2 13 61 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 122 180 (accept_3_4 25 122 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 122 180 2 12 61 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 122 180
  (Polychromatic418967fa.accept_7_2_3_5_1_34 23 122 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 122 180 2 11 61 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 122 180 (Polychromatic418967fa.accept_23_21_7_19_1_10347 21 122 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 122 180 2 10 61 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 122 180 (accept_3_4 19 122 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 122 180 2 9 61 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 122 180
  (Polychromatic418967fa.accept_19_17_8_9_1_10148 17 122 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 122 180 2 8 61 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 122 180 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 122 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 122 180 2 7 61 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 122 180 (accept_3_4 13 122 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 122 180 2 6 61 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 122 180
  (Polychromatic418967fa.accept_17_11_3_10_1_2838 11 122 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 122 180 2 5 61 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 122 180 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 122 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 122 180 2 4 61 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 122 180 (accept_3_4 7 122 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 122 180 2 3 61 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 122 180 (Polychromatic418967fa.accept_14_5_10_12_1_1454 5 122
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 122 180 2 2 61 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 122 180
  (Polychromatic418967fa.accept_13_3_5_11_1_716 3 122 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 122 180 2 1 61 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 122 180 (accept_3_4 1 122 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  180))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 121 180 (Eq.refl Bool.true)
  (allA_succ_of_accept 59 121 180 (accept_3_5 59 121 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 121 180 (Polychromatic418967fa.accept_13_6_4_11_1_282 58 121 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 121 180 (Polychromatic418967fa.accept_27_3_13_18_1_10346 57 121 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 121 180 (accept_3_5 56 121 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 121 180 (Polychromatic418967fa.accept_19_17_7_9_1_3324 55 121
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 121 180
  (Polychromatic418967fa.accept_13_2_4_11_1_2003 54 121 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 121 180 (accept_3_5 53 121 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 121 180 (Polychromatic418967fa.accept_7_3_2_5_1_147 52 121 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 121 180 (Polychromatic418967fa.accept_13_12_4_11_1_1925 51 121 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 121 180 (accept_3_5 50 121 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 121 180 (Polychromatic418967fa.accept_13_10_4_11_1_1969 49 121
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 121 180
  (Polychromatic418967fa.accept_19_10_7_9_1_10345 48 121 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 121 180 (accept_3_5 47 121 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 121 180 (Polychromatic418967fa.accept_7_4_2_5_1_527 46 121 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 121 180 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 121 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 121 180 (accept_3_5 44 121 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 121 180
  (Polychromatic418967fa.accept_16_11_9_4_1_5438 43 121 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 121 180 (Polychromatic418967fa.accept_17_8_2_10_1_2879 42 121 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 121 180 (accept_3_5 41 121 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 121 180 (Polychromatic418967fa.accept_16_8_9_4_1_630 40 121 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 121 180
  (Polychromatic418967fa.accept_7_4_2_5_1_527 39 121 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 121 180 (accept_3_5 38 121 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 121 180 (Polychromatic418967fa.accept_8_5_1_4_1_628 37 121 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 121 180 (Polychromatic418967fa.accept_13_10_4_11_1_1969 36 121 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 121 180 (accept_3_5 35 121 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 121 180 (Polychromatic418967fa.accept_13_8_4_11_1_3469 34 121
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 121 180
  (Polychromatic418967fa.accept_13_7_4_11_1_1967 33 121 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 121 180 (accept_3_5 32 121 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 121 180 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 121 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 121 180 (Polychromatic418967fa.accept_16_14_9_4_1_6693 30 121 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 121 180 (accept_3_5 29 121 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 121 180 (Polychromatic418967fa.accept_13_2_4_11_1_2003 28 121
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 121 180
  (Polychromatic418967fa.accept_16_11_9_4_1_5438 27 121 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 121 180 (accept_3_5 26 121 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 121 180 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 121 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 121 180 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 121 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 121 180 (accept_3_5 23 121 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 121 180 (Polychromatic418967fa.accept_26_22_17_24_1_10344 22 121 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 121 180
  (Polychromatic418967fa.accept_8_5_1_4_1_628 21 121 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 121 180 (accept_3_5 20 121 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 121 180 (Polychromatic418967fa.accept_13_6_4_11_1_282 19 121 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 121 180 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 121 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 121 180 (accept_3_5 17 121 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 121 180 (Polychromatic418967fa.accept_19_16_7_9_1_7321 16 121 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 121 180
  (Polychromatic418967fa.accept_13_2_4_11_1_2003 15 121 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 121 180 (accept_3_5 14 121 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 121 180 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 121 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 121 180 (Polychromatic418967fa.accept_13_12_4_11_1_1925 12 121 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 121 180 (accept_3_5 11 121 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 121 180 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 121 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 121 180
  (Polychromatic418967fa.accept_21_9_16_12_1_4050 9 121 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 121 180 (accept_3_5 8 121 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  121 180 (Polychromatic418967fa.accept_13_7_4_11_1_1967 7 121 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 121 180 (Polychromatic418967fa.accept_13_6_4_11_1_282 6 121 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 121 180 (accept_3_5 5 121 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 121 180 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 121 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 121 180
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 121 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 121 180 (accept_3_5 2 121 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  121 180 (Polychromatic418967fa.accept_22_1_11_4_1_10343 1 121 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 121 180)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 120 180
  (Eq.refl Bool.true) (allA_succ_of_gcd 60 120 180 60 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 120 180 (Polychromatic418967fa.accept_7_3_1_5_1_44 59 120 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 120 180 2 29 60 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 120 180 3 19 40 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 120 180 4 14 30 45
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 120 180 5 11 24
  36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 120 180 6 9 20
  30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 120 180
  (Polychromatic418967fa.accept_7_4_1_5_1_540 53 120 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 120 180 4 13 30 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 51 120 180 3 17 40 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 50 120 180 10 5 12 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 120 180 (Polychromatic418967fa.accept_11_5_10_4_1_1157 49 120
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 120 180 12 4 10 15 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 120 180
  (Polychromatic418967fa.accept_13_8_3_11_1_3467 47 120 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 120 180 2 23 60 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 120 180 15 3 8 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 44 120 180 4 11 30 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 120 180 (Polychromatic418967fa.accept_16_11_8_4_1_2234 43 120 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 120 180 6 7 20 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 120 180
  (Polychromatic418967fa.accept_7_6_1_5_1_322 41 120 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 120 180 20 2 6 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 120 180 3 13 40 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 38 120 180 2 19 60 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 120 180 (Polychromatic418967fa.accept_16_5_8_4_1_5418 37 120 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 120 180 12 3 10 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 120 180 5 7 24 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 120 180 2 17 60 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 120 180 3 11 40 60
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 120 180 4 8 30 45
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 120 180
  (Polychromatic418967fa.accept_7_3_1_5_1_44 31 120 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 120 180 30 1 4 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 120 180 (Polychromatic418967fa.accept_16_13_8_4_1_3250 29 120 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 120 180 4 7 30 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 120 180 3 9 40 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 120 180 2 13 60 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 120 180 5 5 24 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 120 180 12 2 10 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 120 180
  (Polychromatic418967fa.accept_13_10_3_11_1_1923 23 120 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 120 180 2 11 60 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 21 120 180 3 7 40 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 20 120 180 20 1 6 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 120 180 (Polychromatic418967fa.accept_16_3_8_4_1_3279 19 120 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 120 180 6 3 20 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 120 180
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 120 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 120 180 4 4 30 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 120 180 15 1 8 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 120 180 2 7 60 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 120 180 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 120 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 180 12 1 10 15 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 180 (Polychromatic418967fa.accept_7_4_1_5_1_540 11
  120 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 120 180 10 1 12 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 120 180 3 3 40 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 120 180 4 2 30 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 120 180
  (Polychromatic418967fa.accept_13_7_3_11_1_280 7 120 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 120 180 6 1 20 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 120 180 5 1 24 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 120 180 4 1 30 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 120 180 3 1 40 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 120 180 2 1 60 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 120 180 (Polychromatic418967fa.accept_13_1_3_11_1_1289 1 120 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 120 180)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 62 119 180 (Eq.refl Bool.true) (allA_succ_of_accept 61 119 180 (accept_3_4 61 119 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 119 180 (Polychromatic418967fa.accept_16_12_7_4_1_687 60 119 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 119 180
  (Polychromatic418967fa.accept_8_3_7_4_1_42 59 119 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 119 180 (accept_3_4 58 119 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 119 180 (Polychromatic418967fa.accept_11_2_9_4_1_310 57 119 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 119 180 (Polychromatic418967fa.accept_13_4_2_11_1_733 56 119 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 119 180 (accept_3_4 55 119 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 119 180 (Polychromatic418967fa.accept_23_8_4_19_1_10284 54 119
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 119 180
  (Polychromatic418967fa.accept_19_15_5_9_1_3299 53 119 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 119 180 (accept_3_4 52 119 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 119 180 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 119 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 119 180 (Polychromatic418967fa.accept_19_12_5_9_1_7320 50 119 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 119 180 (accept_3_4 49 119 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 119 180 (Polychromatic418967fa.accept_13_9_2_11_1_1964 48 119
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 119 180
  (Polychromatic418967fa.accept_14_5_7_12_1_4006 47 119 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 119 180 (accept_3_4 46 119 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 119 180 (Polychromatic418967fa.accept_16_13_7_4_1_3248 45 119 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 119 180 (Polychromatic418967fa.accept_14_2_7_12_1_1485 44 119 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 119 180 (accept_3_4 43 119 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 119 180 (Polychromatic418967fa.accept_13_3_2_11_1_1999 42 119
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 119 180
  (Polychromatic418967fa.accept_23_18_4_19_1_10282 41 119 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 119 180 (accept_3_4 40 119 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 119 180 (Polychromatic418967fa.accept_19_1_5_9_1_10341 39 119 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 119 180 (Polychromatic418967fa.accept_22_16_9_4_1_10288 38 119
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 119 180 (accept_3_4 37 119
  180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 119 180
  (Polychromatic418967fa.accept_13_10_2_11_1_1920 36 119 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 119 180 (Polychromatic418967fa.accept_8_3_7_4_1_42 35 119 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 119 180 (accept_3_4 34 119 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 119 180 (Polychromatic418967fa.accept_14_5_7_12_1_4006 33 119 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 119 180
  (Polychromatic418967fa.accept_19_13_5_9_1_3318 32 119 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 119 180 (accept_3_4 31 119 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 119 180 (Polychromatic418967fa.accept_13_4_2_11_1_733 30 119 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 119 180 (Polychromatic418967fa.accept_13_3_2_11_1_1999 29 119 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 119 180 (accept_3_4 28 119 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 119 180 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 119 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 119 180
  (Polychromatic418967fa.accept_19_7_5_9_1_10202 26 119 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 119 180 (accept_3_4 25 119 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 119 180 (Polychromatic418967fa.accept_11_2_9_4_1_310 24 119 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 119 180 (Polychromatic418967fa.accept_13_10_2_11_1_1920 23 119 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 119 180 (accept_3_4 22 119 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 119 180 (Polychromatic418967fa.accept_22_21_9_4_1_10342 21 119
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 119 180
  (Polychromatic418967fa.accept_19_1_5_9_1_10341 20 119 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 119 180 (accept_3_4 19 119 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 119 180 (Polychromatic418967fa.accept_19_18_5_9_1_1112 18 119 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 119 180 (Polychromatic418967fa.accept_13_4_2_11_1_733 17 119 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 119 180 (accept_3_4 16 119 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 119 180 (Polychromatic418967fa.accept_19_15_5_9_1_3299 15 119
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 119 180
  (Polychromatic418967fa.accept_16_14_7_4_1_3243 14 119 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 119 180 (accept_3_4 13 119 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 119 180 (Polychromatic418967fa.accept_16_12_7_4_1_687 12 119 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 119 180 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 119 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 180 (accept_3_4 10 119 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 119 180 (Polychromatic418967fa.accept_13_9_2_11_1_1964 9 119 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 180
  (Polychromatic418967fa.accept_16_8_7_4_1_2217 8 119 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 119 180 (accept_3_4 7 119 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  119 180 (Polychromatic418967fa.accept_21_6_14_12_1_4003 6 119 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 119 180 (Polychromatic418967fa.accept_14_5_7_12_1_4006 5 119 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 180 (accept_3_4 4 119 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 119 180 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 119 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 180
  (Polychromatic418967fa.accept_11_2_9_4_1_310 2 119 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 119 180 (accept_3_4 1 119 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  180)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 118 180 (Eq.refl Bool.true)
  (allA_succ_of_gcd 62 118 180 2 31 59 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 118 180 (Polychromatic418967fa.accept_13_9_1_11_1_275 61 118 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 118 180 2 30 59 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 118 180 (accept_3_5 59 118 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 118 180 2 29 59 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 118 180
  (Polychromatic418967fa.accept_7_1_6_5_1_39 57 118 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 118 180 2 28 59 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 118 180 (Polychromatic418967fa.accept_13_3_1_11_1_1268 55 118 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 118 180 2 27 59 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 118 180 (accept_3_5 53 118 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 118 180 2 26 59 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 118 180
  (Polychromatic418967fa.accept_11_7_8_4_1_718 51 118 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 118 180 2 25 59 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 118 180 (Polychromatic418967fa.accept_13_10_1_11_1_1961 49 118 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 118 180 2 24 59 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 118 180 (accept_3_5 47 118 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 118 180 2 23 59 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 118 180
  (Polychromatic418967fa.accept_11_1_8_4_1_717 45 118 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 118 180 2 22 59 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 118 180 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 118 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 118 180 2 21 59 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 118 180 (accept_3_5 41 118 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 118 180 2 20 59 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 118 180 (Polychromatic418967fa.accept_7_4_6_5_1_141 39
  118 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 118 180 2 19 59 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 118 180
  (Polychromatic418967fa.accept_16_5_6_4_1_3211 37 118 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 118 180 2 18 59 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 118 180 (accept_3_5 35 118 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 118 180 2 17 59 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 118 180 (Polychromatic418967fa.accept_13_7_1_11_1_732 33 118 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 118 180 2 16 59 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 118 180
  (Polychromatic418967fa.accept_22_9_8_4_1_3821 31 118 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 118 180 2 15 59 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 118 180 (accept_3_5 29 118 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 118 180 2 14 59 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 118 180 (Polychromatic418967fa.accept_14_13_6_12_1_3126 27 118 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 118 180 2 13 59 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 118 180
  (Polychromatic418967fa.accept_7_4_6_5_1_141 25 118 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 118 180 2 12 59 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 118 180 (accept_3_5 23 118 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 118 180 2 11 59 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 118 180 (Polychromatic418967fa.accept_13_8_1_11_1_1284 21 118 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 118 180 2 10 59 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 118 180
  (Polychromatic418967fa.accept_16_3_6_4_1_679 19 118 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 118 180 2 9 59 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 118 180 (accept_3_5 17 118 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  118 180 2 8 59 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 118 180 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 118 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 118 180 2 7 59 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 118 180 (Polychromatic418967fa.accept_14_13_6_12_1_3126 13 118 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 118 180 2 6 59 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 118 180 (accept_3_5 11
  118 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 118 180 2 5 59 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 118 180
  (Polychromatic418967fa.accept_13_9_1_11_1_275 9 118 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 118 180 2 4 59 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 118 180 (Polychromatic418967fa.accept_11_7_8_4_1_718 7 118 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 118 180 2 3 59 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 118 180 (accept_3_5 5 118 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 118 180 2 2 59 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 118 180 (Polychromatic418967fa.accept_13_3_1_11_1_1268 3 118 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 118 180 2 1 59 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 118 180 (Polychromatic418967fa.accept_7_1_6_5_1_39 1
  118 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118
  180))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 117 180 (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 117 180 9 7 13 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 117 180 (Polychromatic418967fa.accept_25_12_17_5_1_10340 62 117 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 117 180
  (Polychromatic418967fa.accept_25_11_17_5_1_10339 61 117 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 117 180 3 20 39 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 117 180 (Polychromatic418967fa.accept_14_3_5_12_1_4000 59 117 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 117 180
  (Polychromatic418967fa.accept_11_3_7_4_1_1133 58 117 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 117 180 3 19 39 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 117 180 (Polychromatic418967fa.accept_16_8_5_4_1_674 56 117 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 117 180
  (Polychromatic418967fa.accept_17_4_15_10_1_5139 55 117 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 117 180 9 6 13 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 117 180 (Polychromatic418967fa.accept_17_2_15_10_1_5171 53 117 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 117 180
  (Polychromatic418967fa.accept_11_8_7_4_1_3011 52 117 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 117 180 3 17 39 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 117 180 (Polychromatic418967fa.accept_19_12_3_9_1_10338 50 117 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 117 180
  (Polychromatic418967fa.accept_8_1_5_4_1_388 49 117 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 117 180 3 16 39 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 117 180 (Polychromatic418967fa.accept_11_3_7_4_1_1133 47 117 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 117 180
  (Polychromatic418967fa.accept_26_20_13_24_1_10337 46 117 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 117 180 9 5 13 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 117 180 (Polychromatic418967fa.accept_16_12_5_4_1_3275 44 117 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 180
  (Polychromatic418967fa.accept_24_19_21_12_1_10336 43 117 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 117 180 3 14 39 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 117 180 (Polychromatic418967fa.accept_8_1_5_4_1_388 41 117 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 117 180
  (Polychromatic418967fa.accept_16_8_5_4_1_674 40 117 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 117 180 3 13 39 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 117 180 (Polychromatic418967fa.accept_14_10_5_12_1_3995 38 117 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 180
  (Polychromatic418967fa.accept_19_18_3_9_1_3333 37 117 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 117 180 9 4 13 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 117 180 (Polychromatic418967fa.accept_14_7_5_12_1_1439 35 117 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 180 (Polychromatic418967fa.accept_19_15_3_9_1_5962 34 117
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 117 180 3 11 39 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 117 180
  (Polychromatic418967fa.accept_19_13_3_9_1_5980 32 117 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 117 180 (Polychromatic418967fa.accept_14_3_5_12_1_4000 31 117 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 117 180 3 10 39 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 117 180
  (Polychromatic418967fa.accept_19_10_3_9_1_10335 29 117 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 117 180 (Polychromatic418967fa.accept_16_12_5_4_1_3275 28 117 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 117 180 9 3 13 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 117 180
  (Polychromatic418967fa.accept_27_26_9_18_1_10334 26 117 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 117 180 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 117 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 117 180 3 8 39 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 117 180
  (Polychromatic418967fa.accept_22_1_7_4_1_10333 23 117 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 117 180 (Polychromatic418967fa.accept_16_6_5_4_1_4330 22 117 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 117 180 3 7 39 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 117 180
  (Polychromatic418967fa.accept_25_20_17_5_1_10332 20 117 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 117 180 (Polychromatic418967fa.accept_11_8_7_4_1_3011 19 117 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 117 180 9 2 13 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 117 180
  (Polychromatic418967fa.accept_8_1_5_4_1_388 17 117 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 117 180 (Polychromatic418967fa.accept_25_16_17_5_1_10331 16 117 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 117 180 3 5 39 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 117 180
  (Polychromatic418967fa.accept_11_3_7_4_1_1133 14 117 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 117 180 (Polychromatic418967fa.accept_19_13_3_9_1_5980 13 117 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 117 180 3 4 39 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 117 180 (Polychromatic418967fa.accept_19_11_3_9_1_8882
  11 117 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 180
  (Polychromatic418967fa.accept_14_10_5_12_1_3995 10 117 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 9 117 180 9 1 13 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 117 180 (Polychromatic418967fa.accept_11_8_7_4_1_3011 8 117 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 180 (Polychromatic418967fa.accept_14_7_5_12_1_1439
  7 117 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 117 180 3 2 39 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 117 180
  (Polychromatic418967fa.accept_17_5_15_10_1_10176 5 117 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 117 180 (Polychromatic418967fa.accept_17_4_15_10_1_5139 4 117 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 117 180 3 1 39 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 117 180
  (Polychromatic418967fa.accept_17_2_15_10_1_5171 2 117 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 117 180 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 117 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 117 180))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 65 116 180 (Eq.refl Bool.true) (allA_succ_of_gcd 64 116 180 4 16 29 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 116 180
  (Polychromatic418967fa.accept_25_13_16_5_1_10330 63 116 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 116 180 2 31 58 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 116 180 (accept_3_4 61 116 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 116 180 4 15 29 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 116 180 (Polychromatic418967fa.accept_13_7_12_11_1_1911 59 116 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 116 180 2 29 58 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 116 180
  (Polychromatic418967fa.accept_7_1_4_5_1_35 57 116 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 116 180 4 14 29 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 116 180 (accept_3_4 55 116 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 116 180 2 27 58 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 116 180 (Polychromatic418967fa.accept_13_1_12_11_1_728 53 116 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 116 180 4 13 29 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 116 180
  (Polychromatic418967fa.accept_7_2_4_5_1_313 51 116 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 116 180 2 25 58 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 116 180 (accept_3_4 49 116 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 116 180 4 12 29 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 116 180 (Polychromatic418967fa.accept_17_13_14_10_1_1847 47 116 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 116 180 2 23 58 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 116 180
  (Polychromatic418967fa.accept_19_7_2_9_1_6006 45 116 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 116 180 4 11 29 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 116 180 (accept_3_4 43 116 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 116 180 2 21 58 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 116 180 (Polychromatic418967fa.accept_7_6_4_5_1_314 41 116 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 116 180 4 10 29 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 116 180
  (Polychromatic418967fa.accept_17_5_14_10_1_2831 39 116 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 116 180 2 19 58 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 116 180 (accept_3_4 37 116 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 116 180 4 9 29 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 116 180 (Polychromatic418967fa.accept_11_2_6_4_1_3028 35 116 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 116 180 2 17 58 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 116 180
  (Polychromatic418967fa.accept_13_7_12_11_1_1911 33 116 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 116 180 4 8 29 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 116 180 (accept_3_4 31 116 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 116 180 2 15 58 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 116 180 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 116 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 116 180 4 7 29 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 116 180
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 116 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 116 180 2 13 58 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 116 180 (accept_3_4 25 116 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 116 180 4 6 29 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 116 180 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 116 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 116 180 2 11 58 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 116 180
  (Polychromatic418967fa.accept_25_21_16_5_1_10329 21 116 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 116 180 4 5 29 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 116 180 (accept_3_4 19 116 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 116 180 2 9 58 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 116 180 (Polychromatic418967fa.accept_13_4_12_11_1_5362 17 116 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 116 180 4 4 29 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 116 180
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 116 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 116 180 2 7 58 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 116 180 (accept_3_4 13 116 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12
  116 180 4 3 29 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  11 116 180 (Polychromatic418967fa.accept_19_11_2_9_1_8897 11 116 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 116 180 2 5 58 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 116 180 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 116 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 116 180 4 2 29 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 116 180 (accept_3_4 7 116 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 116 180 2 3 58 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 116 180 (Polychromatic418967fa.accept_17_5_14_10_1_2831 5 116
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 116 180 4 1 29 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 116 180
  (Polychromatic418967fa.accept_21_3_11_12_1_10183 3 116 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 116 180 2 1 58 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 116 180 (accept_3_4 1 116 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  180))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 115 180 (Eq.refl Bool.true)
  (allA_succ_of_gcd 65 115 180 5 13 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 64 115 180 (Polychromatic418967fa.accept_7_1_3_5_1_33 64 115 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 115 180 (Polychromatic418967fa.accept_8_7_3_4_1_404
  63 115 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 115 180 (accept_3_5 62
  115 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 115 180
  (Polychromatic418967fa.accept_14_5_3_12_1_324 61 115 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 115 180 5 12 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 115 180 (accept_3_5 59 115 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 115 180 (Polychromatic418967fa.accept_7_2_3_5_1_34 58 115 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 115 180 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 115 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 115 180 (accept_3_5 56 115 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 115 180 5 11 23 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 115 180
  (Polychromatic418967fa.accept_11_10_5_4_1_711 54 115 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 115 180 (accept_3_5 53 115 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 115 180 (Polychromatic418967fa.accept_19_14_1_9_1_10328 52 115 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 115 180 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 115 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 115 180 5 10 23 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 115 180
  (Polychromatic418967fa.accept_16_1_3_4_1_665 49 115 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 115 180 (Polychromatic418967fa.accept_17_14_13_10_1_3936 48 115 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 115 180 (accept_3_5 47 115 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 115 180 (Polychromatic418967fa.accept_19_8_1_9_1_7329 46 115 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 115 180 5 9 23 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 115 180 (accept_3_5 44 115 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 115 180 (Polychromatic418967fa.accept_7_1_3_5_1_33 43
  115 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 115 180
  (Polychromatic418967fa.accept_24_18_19_12_1_10327 42 115 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 115 180 (accept_3_5 41 115 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 115 180 5 8 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 115 180 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 115 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 115 180 (accept_3_5 38 115 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 115 180 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 115 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 115 180 (Polychromatic418967fa.accept_7_1_3_5_1_33 36
  115 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 115 180 5 7 23 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 115 180
  (Polychromatic418967fa.accept_22_12_5_4_1_10326 34 115 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 115 180 (Polychromatic418967fa.accept_14_5_3_12_1_324 33 115 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 115 180 (accept_3_5 32 115 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 115 180 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 115 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 115 180 5 6 23 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 115 180 (accept_3_5 29
  115 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 115 180
  (Polychromatic418967fa.accept_16_12_3_4_1_4317 28 115 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 115 180 (Polychromatic418967fa.accept_19_8_1_9_1_7329 27 115 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 115 180 (accept_3_5 26 115 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 115 180 5 5 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 24 115 180 (Polychromatic418967fa.accept_16_8_3_4_1_3233 24 115 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 115 180 (accept_3_5 23 115 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 115 180 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 115 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 115 180
  (Polychromatic418967fa.accept_11_10_5_4_1_711 21 115 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 115 180 5 4 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 115 180 (Polychromatic418967fa.accept_14_5_3_12_1_324 19 115 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 115 180 (Polychromatic418967fa.accept_22_18_5_4_1_10325 18 115
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 115 180 (accept_3_5 17 115
  180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 115 180
  (Polychromatic418967fa.accept_7_2_3_5_1_34 16 115 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 115 180 5 3 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 115 180 (accept_3_5 14 115 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 115 180 (Polychromatic418967fa.accept_26_13_11_24_1_10324 13 115 180 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 115 180 (Polychromatic418967fa.accept_16_12_3_4_1_4317 12 115 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 115 180 (accept_3_5 11 115 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 115 180 5 2 23 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 115 180
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 115 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 115 180 (accept_3_5 8 115 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  115 180 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 115 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 115 180 (Polychromatic418967fa.accept_16_6_3_4_1_6624 6 115 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 115 180 5 1 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 115 180
  (Polychromatic418967fa.accept_24_4_19_12_1_10276 4 115 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 115 180 (Polychromatic418967fa.accept_17_3_13_10_1_3935 3 115 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 180 (accept_3_5 2 115 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 115 180 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 115 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115
  180)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 114 180 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 114 180 6 11 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 114 180 (Polychromatic418967fa.accept_21_2_9_12_1_4040 65 114 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 114 180 2 32 57 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 114 180 3 21 38 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 114 180 2 31 57 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 114 180
  (Polychromatic418967fa.accept_21_19_9_12_1_4071 61 114 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 114 180 6 10 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 114 180 (Polychromatic418967fa.accept_7_3_2_5_1_147 59 114 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 114 180 2 29 57 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 114 180 3 19 38 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 114 180 2 28 57 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 114 180
  (Polychromatic418967fa.accept_13_3_10_11_1_1293 55 114 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 114 180 6 9 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 114 180 (Polychromatic418967fa.accept_7_4_2_5_1_527 53 114 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 114 180 2 26 57 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 114 180 3 17 38 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 114 180 2 25 57 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 114 180
  (Polychromatic418967fa.accept_14_7_2_12_1_1430 49 114 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 114 180 6 8 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 114 180 (Polychromatic418967fa.accept_13_8_10_11_1_2730 47 114 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 114 180 2 23 57 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 114 180 3 15 38 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 114 180 2 22 57 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 114 180
  (Polychromatic418967fa.accept_13_4_10_11_1_1908 43 114 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 114 180 6 7 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 114 180 (Polychromatic418967fa.accept_13_2_10_11_1_1276 41 114 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 114 180 2 20 57 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 114 180 3 13 38 60
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 114 180 2 19 57
  90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 114 180
  (Polychromatic418967fa.accept_21_16_9_12_1_8697 37 114 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 114 180 6 6 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 114 180 (Polychromatic418967fa.accept_14_7_2_12_1_1430 35 114 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 114 180 2 17 57 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 114 180 3 11 38 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 114 180 2 16 57 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 114 180
  (Polychromatic418967fa.accept_7_3_2_5_1_147 31 114 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 114 180 6 5 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 114 180 (Polychromatic418967fa.accept_13_3_10_11_1_1293 29 114 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 114 180 2 14 57 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 114 180 3 9 38 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 114 180 2 13 57 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 114 180
  (Polychromatic418967fa.accept_7_4_2_5_1_527 25 114 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 114 180 6 4 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 114 180 (Polychromatic418967fa.accept_17_6_12_10_1_7781 23 114 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 114 180 2 11 57 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 114 180 3 7 38 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 114 180 2 10 57 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 114 180
  (Polychromatic418967fa.accept_17_2_12_10_1_9034 19 114 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 114 180 6 3 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 114 180 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 114 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 114 180 2 8 57 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 114 180 3 5 38 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 114 180 2 7 57 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 114 180
  (Polychromatic418967fa.accept_21_13_9_12_1_4038 13 114 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 114 180 6 2 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 114 180 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 114 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 114 180 2 5 57 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 114 180 3 3 38 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 114 180 2 4 57 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 114 180
  (Polychromatic418967fa.accept_14_7_2_12_1_1430 7 114 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 114 180 6 1 19 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 114 180 (Polychromatic418967fa.accept_17_5_12_10_1_3963 5 114 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 114 180 2 2 57 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 114 180 3 1 38 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 114 180 2 1 57 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 180 (Polychromatic418967fa.accept_13_1_10_11_1_1280 1 114
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  180))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 113 180 (Eq.refl Bool.true)
  (allA_succ_of_accept 67 113 180 (accept_3_4 67 113 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 113 180 (Polychromatic418967fa.accept_7_3_1_5_1_44 66 113 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 113 180 (Polychromatic418967fa.accept_19_8_18_9_1_10160 65 113 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 113 180 (accept_3_4 64 113 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 113 180 (Polychromatic418967fa.accept_19_6_18_9_1_10323 63 113
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 113 180
  (Polychromatic418967fa.accept_7_6_1_5_1_322 62 113 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 113 180 (accept_3_4 61 113 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 113 180 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 113 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 113 180 (Polychromatic418967fa.accept_7_3_1_5_1_44 59 113 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 113 180 (accept_3_4 58 113 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 113 180 (Polychromatic418967fa.accept_21_15_8_12_1_8687 57 113 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 113 180
  (Polychromatic418967fa.accept_16_8_1_4_1_6622 56 113 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 113 180 (accept_3_4 55 113 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 113 180 (Polychromatic418967fa.accept_13_2_9_11_1_258 54 113 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 113 180 (Polychromatic418967fa.accept_7_4_1_5_1_540 53 113 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 113 180 (accept_3_4 52 113 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 113 180 (Polychromatic418967fa.accept_11_7_3_4_1_729 51 113 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 113 180
  (Polychromatic418967fa.accept_19_12_18_9_1_7352 50 113 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 113 180 (accept_3_4 49 113 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 113 180 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 113 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 113 180 (Polychromatic418967fa.accept_13_8_9_11_1_1265 47 113
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 113 180 (accept_3_4 46 113
  180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 113 180
  (Polychromatic418967fa.accept_7_3_1_5_1_44 45 113 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 113 180 (Polychromatic418967fa.accept_16_12_1_4_1_5403 44 113 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 113 180 (accept_3_4 43 113 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 113 180 (Polychromatic418967fa.accept_24_18_17_12_1_3252 42 113 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 113 180
  (Polychromatic418967fa.accept_7_6_1_5_1_322 41 113 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 113 180 (accept_3_4 40 113 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 113 180 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 113 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 113 180 (Polychromatic418967fa.accept_7_3_1_5_1_44 38 113 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 113 180 (accept_3_4 37 113 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 113 180 (Polychromatic418967fa.accept_21_15_8_12_1_8687 36 113 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 113 180
  (Polychromatic418967fa.accept_16_3_1_4_1_5426 35 113 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 113 180 (accept_3_4 34 113 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 113 180 (Polychromatic418967fa.accept_13_7_9_11_1_705 33 113 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 113 180 (Polychromatic418967fa.accept_7_4_1_5_1_540 32 113 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 113 180 (accept_3_4 31 113 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 113 180 (Polychromatic418967fa.accept_16_14_1_4_1_5432 30 113 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 113 180
  (Polychromatic418967fa.accept_8_5_1_4_1_628 29 113 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 113 180 (accept_3_4 28 113 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 113 180 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 113 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 113 180 (Polychromatic418967fa.accept_21_5_8_12_1_7108 26 113 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 113 180 (accept_3_4 25 113 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 113 180 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 113 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 113 180
  (Polychromatic418967fa.accept_22_1_3_4_1_10322 23 113 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 113 180 (accept_3_4 22 113 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 113 180 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 113 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 113 180 (Polychromatic418967fa.accept_7_6_1_5_1_322 20 113 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 113 180 (accept_3_4 19 113 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 113 180 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 113 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 113 180
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 113 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 113 180 (accept_3_4 16 113 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 113 180 (Polychromatic418967fa.accept_13_2_9_11_1_258 15 113 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 113 180 (Polychromatic418967fa.accept_13_1_9_11_1_703 14 113 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 113 180 (accept_3_4 13 113 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 113 180 (Polychromatic418967fa.accept_16_12_1_4_1_5403 12 113
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 113 180
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 113 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 113 180 (accept_3_4 10 113 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  113 180 (Polychromatic418967fa.accept_21_9_8_12_1_10321 9 113 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 113 180 (Polychromatic418967fa.accept_13_8_9_11_1_1265 8 113 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 113 180 (accept_3_4 7 113 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 113 180 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 113 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 113 180
  (Polychromatic418967fa.accept_8_5_1_4_1_628 5 113 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 113 180 (accept_3_4 4 113 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  113 180 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 113 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 113 180 (Polychromatic418967fa.accept_13_2_9_11_1_258 2 113 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 113 180 (accept_3_4 1 113 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 113 180)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  69 112 180 (Eq.refl Bool.true) (allA_succ_of_gcd 68 112 180 4 17 28 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 112 180
  (Polychromatic418967fa.accept_21_4_7_12_1_10320 67 112 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 112 180 2 33 56 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 112 180 (accept_3_5 65 112 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 112 180 4 16 28 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 112 180 (Polychromatic418967fa.accept_19_6_17_9_1_10318 63 112 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 112 180 2 31 56 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 112 180
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 61 112 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 112 180 4 15 28 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 112 180 (accept_3_5 59 112 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 112 180 2 29 56 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 112 180 (Polychromatic418967fa.accept_21_15_7_12_1_8686 57 112 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 112 180 4 14 28 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 112 180
  (Polychromatic418967fa.accept_13_3_8_11_1_1906 55 112 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 112 180 2 27 56 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 112 180 (accept_3_5 53 112 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 112 180 4 13 28 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 112 180 (Polychromatic418967fa.accept_19_13_17_9_1_3312 51 112 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 112 180 2 25 56 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 112 180
  (Polychromatic418967fa.accept_13_10_8_11_1_1985 49 112 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 112 180 4 12 28 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 112 180 (accept_3_5 47 112 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 112 180 2 23 56 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 112 180 (Polychromatic418967fa.accept_13_6_8_11_1_5398 45 112 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 112 180 4 11 28 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 112 180
  (Polychromatic418967fa.accept_13_4_8_11_1_1937 43 112 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 112 180 2 21 56 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 112 180 (accept_3_5 41 112 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 112 180 4 10 28 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 112 180 (Polychromatic418967fa.accept_11_6_2_4_1_1703 39 112 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 112 180 2 19 56 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 112 180
  (Polychromatic418967fa.accept_21_16_7_12_1_10319 37 112 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 112 180 4 9 28 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 112 180 (accept_3_5 35 112 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 112 180 2 17 56 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 112 180 (Polychromatic418967fa.accept_19_14_17_9_1_5959 33 112 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 112 180 4 8 28 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 112 180
  (Polychromatic418967fa.accept_11_9_2_4_1_707 31 112 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 112 180 2 15 56 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 112 180 (accept_3_5 29 112 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 112 180 4 7 28 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 112 180 (Polychromatic418967fa.accept_13_1_8_11_1_724 27 112 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 112 180 2 13 56 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 112 180
  (Polychromatic418967fa.accept_19_6_17_9_1_10318 25 112 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 112 180 4 6 28 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 112 180 (accept_3_5 23 112 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 112 180 2 11 56 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 112 180 (Polychromatic418967fa.accept_19_2_17_9_1_10317 21 112 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 112 180 4 5 28 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 112 180
  (Polychromatic418967fa.accept_13_6_8_11_1_5398 19 112 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 112 180 2 9 56 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 112 180 (accept_3_5 17 112 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  112 180 4 4 28 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 112 180 (Polychromatic418967fa.accept_21_15_7_12_1_8686 15 112 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 112 180 2 7 56 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 112 180 (Polychromatic418967fa.accept_19_13_17_9_1_3312 13 112 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 112 180 4 3 28 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 112 180 (accept_3_5 11
  112 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 112 180 2 5 56 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 112 180
  (Polychromatic418967fa.accept_11_9_2_4_1_707 9 112 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 112 180 4 2 28 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 112 180 (Polychromatic418967fa.accept_19_7_17_9_1_8879 7 112 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 112 180 2 3 56 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 112 180 (accept_3_5 5 112 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 112 180 4 1 28 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 112 180 (Polychromatic418967fa.accept_13_3_8_11_1_1906 3 112 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 112 180 2 1 56 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 112 180 (Polychromatic418967fa.accept_13_1_8_11_1_724 1
  112 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112
  180))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 111 180 (Eq.refl Bool.true)
  (allA_succ_of_gcd 69 111 180 3 23 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 111 180 (Polychromatic418967fa.accept_13_3_7_11_1_1904 68 111 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 180
  (Polychromatic418967fa.accept_7_4_6_5_1_141 67 111 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 111 180 3 22 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 111 180 (Polychromatic418967fa.accept_19_8_16_9_1_8847 65 111 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 111 180
  (Polychromatic418967fa.accept_7_1_6_5_1_39 64 111 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 111 180 3 21 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 111 180 (Polychromatic418967fa.accept_14_6_13_12_1_810 62 111 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 111 180
  (Polychromatic418967fa.accept_13_9_7_11_1_1292 61 111 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 111 180 3 20 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 111 180 (Polychromatic418967fa.accept_8_3_7_4_1_42 59 111 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 111 180
  (Polychromatic418967fa.accept_21_16_6_12_1_2706 58 111 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 57 111 180 3 19 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 56 111 180 (Polychromatic418967fa.accept_13_4_7_11_1_1981 56 111 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 180
  (Polychromatic418967fa.accept_13_3_7_11_1_1904 55 111 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 111 180 3 18 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 111 180 (Polychromatic418967fa.accept_7_4_6_5_1_141 53 111 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 111 180 (Polychromatic418967fa.accept_11_8_1_4_1_2318
  52 111 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 111 180 3 17 37 60
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 111 180
  (Polychromatic418967fa.accept_7_1_6_5_1_39 50 111 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 111 180 (Polychromatic418967fa.accept_21_7_6_12_1_10316 49 111 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 111 180 3 16 37 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 111 180
  (Polychromatic418967fa.accept_17_13_9_10_1_2888 47 111 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 111 180 (Polychromatic418967fa.accept_7_4_6_5_1_141 46 111 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 111 180 3 15 37 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 111 180
  (Polychromatic418967fa.accept_13_5_7_11_1_3470 44 111 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 111 180 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 111 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 111 180 3 14 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 111 180 (Polychromatic418967fa.accept_11_8_1_4_1_2318
  41 111 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 111 180
  (Polychromatic418967fa.accept_13_1_7_11_1_702 40 111 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 111 180 3 13 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 111 180 (Polychromatic418967fa.accept_13_12_7_11_1_1935 38 111 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 180
  (Polychromatic418967fa.accept_16_5_15_4_1_9099 37 111 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 111 180 3 12 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 111 180 (Polychromatic418967fa.accept_8_3_7_4_1_42 35 111 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 111 180
  (Polychromatic418967fa.accept_14_6_13_12_1_810 34 111 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 111 180 3 11 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 111 180 (Polychromatic418967fa.accept_7_4_6_5_1_141 32 111 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 180
  (Polychromatic418967fa.accept_13_5_7_11_1_3470 31 111 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 111 180 3 10 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 111 180 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 111 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 180
  (Polychromatic418967fa.accept_16_12_15_4_1_5422 28 111 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 111 180 3 9 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 111 180 (Polychromatic418967fa.accept_19_7_16_9_1_398 26 111 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 180
  (Polychromatic418967fa.accept_7_4_6_5_1_141 25 111 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 111 180 3 8 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 111 180 (Polychromatic418967fa.accept_19_4_16_9_1_10315 23 111 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 111 180 (Polychromatic418967fa.accept_7_1_6_5_1_39 22
  111 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 111 180 3 7 37 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 111 180
  (Polychromatic418967fa.accept_14_6_13_12_1_810 20 111 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 111 180 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 111 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 111 180 3 6 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 111 180 (Polychromatic418967fa.accept_13_4_7_11_1_1981
  17 111 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 180
  (Polychromatic418967fa.accept_13_3_7_11_1_1904 16 111 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 111 180 3 5 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 111 180 (Polychromatic418967fa.accept_13_1_7_11_1_702 14 111 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 180 (Polychromatic418967fa.accept_17_13_9_10_1_2888 13 111
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 111 180 3 4 37 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 111 180
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 111 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 111 180 (Polychromatic418967fa.accept_19_10_16_9_1_10157 10 111 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 111 180 3 3 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 111 180 (Polychromatic418967fa.accept_7_1_6_5_1_39 8
  111 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 180
  (Polychromatic418967fa.accept_19_7_16_9_1_398 7 111 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 111 180 3 2 37 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 111 180 (Polychromatic418967fa.accept_13_5_7_11_1_3470 5 111 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 180 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 111 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 111 180 3 1 37 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 111 180
  (Polychromatic418967fa.accept_21_2_6_12_1_5506 2 111 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 111 180 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 111 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 111
  180)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 110 180 (Eq.refl Bool.true)
  (allA_succ_of_gcd 70 110 180 10 7 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 110 180 (Polychromatic418967fa.accept_13_4_6_11_1_2017 69 110 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 110 180 2 34 55 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 110 180 (accept_3_4 67 110 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 110 180 2 33 55 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 110 180 5 13 22 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 110 180 2 32 55 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 110 180
  (Polychromatic418967fa.accept_16_15_14_4_1_6649 63 110 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 110 180 2 31 55 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 110 180 (accept_3_4 61 110 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 110 180 10 6 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 110 180 (Polychromatic418967fa.accept_19_2_15_9_1_7318 59 110 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 110 180 2 29 55 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 110 180
  (Polychromatic418967fa.accept_13_5_6_11_1_1933 57 110 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 110 180 2 28 55 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 55 110 180 5 11 22 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 54 110 180 2 27 55 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 110 180 (Polychromatic418967fa.accept_17_2_8_10_1_2870 53 110
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 110 180 2 26 55 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 110 180
  (Polychromatic418967fa.accept_19_13_15_9_1_3293 51 110 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 110 180 10 5 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 110 180 (accept_3_4 49 110 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 110 180 2 24 55 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 110 180 (Polychromatic418967fa.accept_13_8_6_11_1_1979 47 110 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 110 180 2 23 55 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 110 180 5 9 22 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 110 180 2 22 55 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 110 180 (accept_3_4 43
  110 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 110 180 2 21 55 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 110 180
  (Polychromatic418967fa.accept_16_9_14_4_1_3225 41 110 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 110 180 10 4 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 110 180 (Polychromatic418967fa.accept_16_7_14_4_1_1362 39 110 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 110 180 2 19 55 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 110 180 (accept_3_4 37 110 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 110 180 2 18 55 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 110 180 5 7 22 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 110 180 2 17 55 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 110 180
  (Polychromatic418967fa.accept_16_1_14_4_1_3220 33 110 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 110 180 2 16 55 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 110 180 (accept_3_4 31 110 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 110 180 10 3 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 110 180 (Polychromatic418967fa.accept_17_12_8_10_1_6440 29 110 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 110 180 2 14 55 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 110 180
  (Polychromatic418967fa.accept_21_6_5_12_1_10314 27 110 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 110 180 2 13 55 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 25 110 180 5 5 22 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 110 180 2 12 55 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 110 180 (Polychromatic418967fa.accept_16_7_14_4_1_1362 23 110
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 110 180 2 11 55 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 110 180
  (Polychromatic418967fa.accept_13_8_6_11_1_1979 21 110 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 110 180 10 2 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 110 180 (accept_3_4 19 110 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 110 180 2 9 55 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 110 180 (Polychromatic418967fa.accept_13_4_6_11_1_2017 17 110 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 110 180 2 8 55 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 110 180 5 3 22 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 110 180 2 7 55 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 110 180 (accept_3_4 13 110 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 110 180 2 6 55 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 110 180 (Polychromatic418967fa.accept_19_11_15_9_1_6002 11 110
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 110 180 10 1 11 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 110 180
  (Polychromatic418967fa.accept_16_9_14_4_1_3225 9 110 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 110 180 2 4 55 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 110 180 (accept_3_4 7 110 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 110
  180 2 3 55 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 110
  180 5 1 22 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 110
  180 2 2 55 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  110 180 (Polychromatic418967fa.accept_19_3_15_9_1_4576 3 110 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 110 180 2 1 55 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 110 180 (accept_3_4 1 110 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  180))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 109 180 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 109 180 (accept_3_5 71 109 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 109 180 (Polychromatic418967fa.accept_16_6_13_4_1_643 70 109 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 109 180 (Polychromatic418967fa.accept_7_6_4_5_1_314 69 109 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 109 180 (accept_3_5 68 109 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 109 180 (Polychromatic418967fa.accept_17_16_7_10_1_5179 67 109 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 109 180
  (Polychromatic418967fa.accept_21_3_4_12_1_1462 66 109 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 109 180 (accept_3_5 65 109 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 109 180 (Polychromatic418967fa.accept_7_1_4_5_1_35 64 109 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 109 180 (Polychromatic418967fa.accept_19_6_14_9_1_8863 63 109 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 109 180 (accept_3_5 62 109 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 109 180 (Polychromatic418967fa.accept_19_4_14_9_1_10227 61 109
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 109 180
  (Polychromatic418967fa.accept_11_5_10_4_1_1157 60 109 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 109 180 (accept_3_5 59 109 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 109 180 (Polychromatic418967fa.accept_7_2_4_5_1_313 58 109 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 109 180 (Polychromatic418967fa.accept_7_1_4_5_1_35 57 109 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 109 180 (accept_3_5 56 109 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 109 180 (Polychromatic418967fa.accept_7_6_4_5_1_314 55 109 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 109 180
  (Polychromatic418967fa.accept_16_6_13_4_1_643 54 109 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 109 180 (accept_3_5 53 109 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 109 180 (Polychromatic418967fa.accept_17_1_7_10_1_1835 52 109 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 109 180 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 109 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 109 180 (accept_3_5 50 109 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 109 180 (Polychromatic418967fa.accept_8_1_5_4_1_388 49 109 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 109 180
  (Polychromatic418967fa.accept_7_6_4_5_1_314 48 109 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 109 180 (accept_3_5 47 109 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 109 180 (Polychromatic418967fa.accept_13_7_5_11_1_1927 46 109 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 109 180 (Polychromatic418967fa.accept_13_6_5_11_1_1971 45 109 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 109 180 (accept_3_5 44 109 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 109 180 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 109 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 109 180
  (Polychromatic418967fa.accept_13_3_5_11_1_716 42 109 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 109 180 (accept_3_5 41 109 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 109 180 (Polychromatic418967fa.accept_16_8_13_4_1_3258 40 109 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 109 180 (Polychromatic418967fa.accept_16_7_13_4_1_1348 39 109 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 109 180 (accept_3_5 38 109 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 109 180 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 109 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 109 180
  (Polychromatic418967fa.accept_7_1_4_5_1_35 36 109 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 109 180 (accept_3_5 35 109 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 109 180 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 109 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 109 180 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 109 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 109 180 (accept_3_5 32 109 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 109 180 (Polychromatic418967fa.accept_17_14_7_10_1_7808 31 109 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 109 180
  (Polychromatic418967fa.accept_7_2_4_5_1_313 30 109 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 109 180 (accept_3_5 29 109 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 109 180 (Polychromatic418967fa.accept_16_12_13_4_1_3198 28 109 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 109 180 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 109 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 109 180 (accept_3_5 26 109 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 109 180 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 109 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 109 180
  (Polychromatic418967fa.accept_16_8_13_4_1_3258 24 109 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 109 180 (accept_3_5 23 109 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 109 180 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 109 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 109 180 (Polychromatic418967fa.accept_23_21_17_19_1_10313 21 109 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 109 180 (accept_3_5 20 109 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 109 180 (Polychromatic418967fa.accept_13_6_5_11_1_1971 19 109
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 109 180
  (Polychromatic418967fa.accept_17_1_7_10_1_1835 18 109 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 109 180 (accept_3_5 17 109 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 109 180 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 109 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 109 180 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 109 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 109 180 (accept_3_5 14 109 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 109 180 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 109 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 109 180
  (Polychromatic418967fa.accept_16_12_13_4_1_3198 12 109 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 109 180 (accept_3_5 11 109 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 109 180 (Polychromatic418967fa.accept_26_10_5_24_1_10312 10 109 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 109 180 (Polychromatic418967fa.accept_7_2_4_5_1_313 9
  109 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 109 180 (accept_3_5 8 109
  180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 109 180
  (Polychromatic418967fa.accept_13_7_5_11_1_1927 7 109 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 109 180 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 109 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 109 180 (accept_3_5 5 109 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 109 180 (Polychromatic418967fa.accept_19_4_14_9_1_10227 4 109 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 109 180
  (Polychromatic418967fa.accept_13_3_5_11_1_716 3 109 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 109 180 (accept_3_5 2 109 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  109 180 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 109 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 109 180)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73
  108 180 (Eq.refl Bool.true) (allA_succ_of_gcd 72 108 180 36 2 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 108 180 (Polychromatic418967fa.accept_7_1_3_5_1_33 71 108 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 108 180 2 35 54 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 108 180 3 23 36 60
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 108 180 4 17 27
  45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 108 180
  (Polychromatic418967fa.accept_13_2_4_11_1_2003 67 108 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 108 180 6 11 18 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 108 180 (Polychromatic418967fa.accept_7_2_3_5_1_34 65 108 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 108 180 4 16 27 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 108 180 9 7 12 20 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 108 180 2 31 54 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 108 180
  (Polychromatic418967fa.accept_14_5_10_12_1_1454 61 108 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 108 180 12 5 9 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 108 180 (Polychromatic418967fa.accept_13_7_4_11_1_1967 59 108 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 108 180 2 29 54 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 108 180 3 19 36 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 108 180 4 14 27 45
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 108 180
  (Polychromatic418967fa.accept_16_7_12_4_1_1347 55 108 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 108 180 18 3 6 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 108 180 (Polychromatic418967fa.accept_16_5_12_4_1_4325 53 108 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 108 180 4 13 27 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 108 180 3 17 36 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 108 180 2 25 54 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 108 180
  (Polychromatic418967fa.accept_13_10_4_11_1_1969 49 108 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 108 180 12 4 9 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 108 180 (Polychromatic418967fa.accept_13_8_4_11_1_3469 47 108 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 108 180 2 23 54 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 108 180 9 5 12 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 108 180 4 11 27 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 108 180
  (Polychromatic418967fa.accept_7_1_3_5_1_33 43 108 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 108 180 6 7 18 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 108 180 (Polychromatic418967fa.accept_13_2_4_11_1_2003 41 108 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 108 180 4 10 27 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 108 180 3 13 36 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 108 180 2 19 54 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 108 180
  (Polychromatic418967fa.accept_7_2_3_5_1_34 37 108 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 108 180 36 1 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 108 180 (Polychromatic418967fa.accept_11_2_9_4_1_310 35 108 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 108 180 2 17 54 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 108 180 3 11 36 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 108 180 4 8 27 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 108 180
  (Polychromatic418967fa.accept_16_15_12_4_1_4324 31 108 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 108 180 6 5 18 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 108 180 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 108 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 108 180 4 7 27 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 108 180 9 3 12 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 108 180 2 13 54 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 108 180
  (Polychromatic418967fa.accept_13_12_4_11_1_1925 25 108 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 108 180 12 2 9 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 108 180 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 108 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 108 180 2 11 54 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 108 180 3 7 36 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 108 180 4 5 27 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 108 180
  (Polychromatic418967fa.accept_13_6_4_11_1_282 19 108 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 108 180 18 1 6 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 108 180 (Polychromatic418967fa.accept_16_1_12_4_1_695 17 108 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 108 180 4 4 27 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 108 180 3 5 36 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 108 180 2 7 54 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 108 180 (Polychromatic418967fa.accept_11_2_9_4_1_310
  13 108 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 108 180 12 1 9 15
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 108 180
  (Polychromatic418967fa.accept_16_11_12_4_1_3195 11 108 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 108 180 2 5 54 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 9 108 180 9 1 12 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 8 108 180 4 2 27 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 7 108 180 (Polychromatic418967fa.accept_13_7_4_11_1_1967 7 108 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 180 6 1 18 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 180
  (Polychromatic418967fa.accept_14_5_10_12_1_1454 5 108 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 108 180 4 1 27 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 108 180 3 1 36 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 108 180 2 1 54 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 108 180 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 108 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 108
  180))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 107 180 (Eq.refl
  Bool.true) (allA_succ_of_accept 73 107 180 (accept_3_4 73 107 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 107 180 (Polychromatic418967fa.accept_13_7_3_11_1_280 72 107 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 107 180 (Polychromatic418967fa.accept_8_7_3_4_1_404 71 107 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 107 180 (accept_3_4 70 107 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 107 180
  (Polychromatic418967fa.accept_21_6_2_12_1_4066 69 107 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 107 180 (Polychromatic418967fa.accept_23_22_15_19_1_8589 68 107 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 107 180 (accept_3_4 67 107 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 107 180 (Polychromatic418967fa.accept_7_3_2_5_1_147 66 107 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 107 180
  (Polychromatic418967fa.accept_17_14_5_10_1_9052 65 107 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 107 180 (accept_3_4 64 107 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 107 180 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 107 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 107 180 (Polychromatic418967fa.accept_11_7_8_4_1_718 62 107
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 107 180 (accept_3_4 61 107
  180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 107 180
  (Polychromatic418967fa.accept_7_4_2_5_1_527 60 107 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 107 180 (Polychromatic418967fa.accept_7_3_2_5_1_147 59 107 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 107 180 (accept_3_4 58 107 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 107 180 (Polychromatic418967fa.accept_13_5_3_11_1_1288 57 107 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 107 180
  (Polychromatic418967fa.accept_11_1_8_4_1_717 56 107 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 107 180 (accept_3_4 55 107 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 107 180 (Polychromatic418967fa.accept_13_2_3_11_1_1287 54 107 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 107 180 (Polychromatic418967fa.accept_7_4_2_5_1_527 53 107 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 107 180 (accept_3_4 52 107 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 107 180 (Polychromatic418967fa.accept_11_7_8_4_1_718 51 107 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 107 180
  (Polychromatic418967fa.accept_23_4_15_19_1_10311 50 107 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 107 180 (accept_3_4 49 107 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 107 180 (Polychromatic418967fa.accept_17_14_5_10_1_9052 48 107 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 107 180 (Polychromatic418967fa.accept_8_7_3_4_1_404
  47 107 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 107 180 (accept_3_4 46
  107 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 107 180
  (Polychromatic418967fa.accept_7_3_2_5_1_147 45 107 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 107 180 (Polychromatic418967fa.accept_13_5_3_11_1_1288 44 107 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 107 180 (accept_3_4 43 107 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 107 180 (Polychromatic418967fa.accept_24_18_11_12_1_10310 42 107 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 107 180
  (Polychromatic418967fa.accept_13_2_3_11_1_1287 41 107 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 107 180 (accept_3_4 40 107 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 107 180 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 107 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 107 180 (Polychromatic418967fa.accept_7_3_2_5_1_147 38 107 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 107 180 (accept_3_4 37 107 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 107 180 (Polychromatic418967fa.accept_13_10_3_11_1_1923 36 107 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 107 180
  (Polychromatic418967fa.accept_14_7_9_12_1_3975 35 107 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 107 180 (accept_3_4 34 107 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 107 180 (Polychromatic418967fa.accept_13_7_3_11_1_280 33 107 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 107 180 (Polychromatic418967fa.accept_7_4_2_5_1_527 32 107 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 107 180 (accept_3_4 31 107 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 107 180 (Polychromatic418967fa.accept_17_13_5_10_1_2839 30 107 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 107 180
  (Polychromatic418967fa.accept_11_7_8_4_1_718 29 107 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 107 180 (accept_3_4 28 107 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 107 180 (Polychromatic418967fa.accept_13_1_3_11_1_1289 27 107 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 107 180 (Polychromatic418967fa.accept_28_26_23_12_1_10309 26 107 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 107 180 (accept_3_4 25 107 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 107 180 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 107 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 107 180
  (Polychromatic418967fa.accept_8_7_3_4_1_404 23 107 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 107 180 (accept_3_4 22 107 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 107 180 (Polychromatic418967fa.accept_13_8_3_11_1_3467 21 107 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 107 180 (Polychromatic418967fa.accept_13_7_3_11_1_280 20 107 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 107 180 (accept_3_4 19 107 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 107 180 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 107 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 107 180
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 107 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 107 180 (accept_3_4 16 107 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 107 180 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 107 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 107 180 (Polychromatic418967fa.accept_13_1_3_11_1_1289 14 107 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 107 180 (accept_3_4 13 107 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 107 180 (Polychromatic418967fa.accept_11_1_8_4_1_717 12 107
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 107 180
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 107 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 107 180 (accept_3_4 10 107 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  107 180 (Polychromatic418967fa.accept_16_9_11_4_1_3194 9 107 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 107 180 (Polychromatic418967fa.accept_13_8_3_11_1_3467 8 107 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 107 180 (accept_3_4 7 107 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 107 180 (Polychromatic418967fa.accept_16_6_11_4_1_635 6 107 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 107 180
  (Polychromatic418967fa.accept_13_5_3_11_1_1288 5 107 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 107 180 (accept_3_4 4 107 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  107 180 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 107 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 107 180 (Polychromatic418967fa.accept_13_2_3_11_1_1287 2 107 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 107 180 (accept_3_4 1 107 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 107
  180)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 106 180 (Eq.refl
  Bool.true) (allA_succ_of_gcd 74 106 180 2 37 53 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 106 180 (Polychromatic418967fa.accept_7_3_1_5_1_44 73 106 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 106 180 2 36 53 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 106 180 (accept_3_5 71 106 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 106 180 2 35 53 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 106 180
  (Polychromatic418967fa.accept_7_6_1_5_1_322 69 106 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 106 180 2 34 53 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 106 180 (Polychromatic418967fa.accept_7_4_1_5_1_540 67 106 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 106 180 2 33 53 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 106 180 (accept_3_5 65 106 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 106 180 2 32 53 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 106 180 (Polychromatic418967fa.accept_11_8_7_4_1_3011
  63 106 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 106 180 2 31 53 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 106 180
  (Polychromatic418967fa.accept_13_9_2_11_1_1964 61 106 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 106 180 2 30 53 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 106 180 (accept_3_5 59 106 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 106 180 2 29 53 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 106 180 (Polychromatic418967fa.accept_17_6_4_10_1_5176 57 106 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 106 180 2 28 53 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 106 180
  (Polychromatic418967fa.accept_7_6_1_5_1_322 55 106 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 106 180 2 27 53 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 106 180 (accept_3_5 53 106 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 106 180 2 26 53 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 106 180 (Polychromatic418967fa.accept_21_9_1_12_1_3984 51 106 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 106 180 2 25 53 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 106 180
  (Polychromatic418967fa.accept_13_10_2_11_1_1920 49 106 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 106 180 2 24 53 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 106 180 (accept_3_5 47 106 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 106 180 2 23 53 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 106 180 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 106 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 106 180 2 22 53 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 106 180
  (Polychromatic418967fa.accept_13_4_2_11_1_733 43 106 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 106 180 2 21 53 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 106 180 (accept_3_5 41 106 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 106 180 2 20 53 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 106 180 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 106 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 106 180 2 19 53 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 106 180
  (Polychromatic418967fa.accept_27_10_25_18_1_10308 37 106 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 106 180 2 18 53 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 106 180 (accept_3_5 35 106 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 106 180 2 17 53 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 106 180 (Polychromatic418967fa.accept_19_14_11_9_1_3330 33 106 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 106 180 2 16 53 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 106 180
  (Polychromatic418967fa.accept_7_3_1_5_1_44 31 106 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 106 180 2 15 53 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 106 180 (accept_3_5 29 106 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 106 180 2 14 53 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 106 180 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 106 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 106 180 2 13 53 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 106 180
  (Polychromatic418967fa.accept_7_4_1_5_1_540 25 106 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 106 180 2 12 53 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 106 180 (accept_3_5 23 106 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 106 180 2 11 53 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 106 180 (Polychromatic418967fa.accept_19_2_11_9_1_1119 21 106 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 106 180 2 10 53 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 106 180
  (Polychromatic418967fa.accept_11_8_7_4_1_3011 19 106 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 106 180 2 9 53 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 106 180 (accept_3_5 17 106 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  106 180 2 8 53 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 106 180 (Polychromatic418967fa.accept_17_15_4_10_1_3968 15 106 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 106 180 2 7 53 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 106 180 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 106 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 106 180 2 6 53 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 106 180 (accept_3_5 11 106 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 106 180 2 5 53 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 106 180
  (Polychromatic418967fa.accept_13_9_2_11_1_1964 9 106 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 106 180 2 4 53 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 106 180 (Polychromatic418967fa.accept_19_7_11_9_1_2139 7 106 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 106 180 2 3 53 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 106 180 (accept_3_5 5 106 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 106 180 2 2 53 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 106 180 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 106 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 106 180 2 1 53 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 106 180 (Polychromatic418967fa.accept_19_1_11_9_1_10307
  1 106 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106
  180))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76 105 180 (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 105 180 15 5 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 105 180 (Polychromatic418967fa.accept_13_9_1_11_1_275 74 105 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 105 180
  (Polychromatic418967fa.accept_13_8_1_11_1_1284 73 105 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 105 180 3 24 35 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 105 180 (Polychromatic418967fa.accept_22_5_17_4_1_10306 71 105 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 105 180 5 14 21 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 105 180 3 23 35 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 105 180
  (Polychromatic418967fa.accept_11_2_6_4_1_3028 68 105 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 105 180 (Polychromatic418967fa.accept_24_19_9_12_1_10305 67 105 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 105 180 3 22 35 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 105 180 5 13 21 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 105 180
  (Polychromatic418967fa.accept_13_12_1_11_1_1917 64 105 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 63 105 180 3 21 35 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 62 105 180 (Polychromatic418967fa.accept_13_10_1_11_1_1961 62 105 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 180
  (Polychromatic418967fa.accept_8_5_1_4_1_628 61 105 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 105 180 15 4 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 105 180 (Polychromatic418967fa.accept_13_7_1_11_1_732 59 105 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 105 180 (Polychromatic418967fa.accept_14_2_7_12_1_1485 58 105
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 105 180 3 19 35 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 105 180
  (Polychromatic418967fa.accept_16_8_9_4_1_630 56 105 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 105 180 5 11 21 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 54 105 180 3 18 35 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 105 180 (Polychromatic418967fa.accept_8_5_1_4_1_628 53 105 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 105 180
  (Polychromatic418967fa.accept_23_6_13_19_1_10304 52 105 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 51 105 180 3 17 35 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 50 105 180 5 10 21 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 105 180 (Polychromatic418967fa.accept_13_10_1_11_1_1961 49 105
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 105 180 3 16 35 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 105 180
  (Polychromatic418967fa.accept_13_8_1_11_1_1284 47 105 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 105 180 (Polychromatic418967fa.accept_11_2_6_4_1_3028 46 105 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 105 180 15 3 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 105 180 (Polychromatic418967fa.accept_14_2_7_12_1_1485
  44 105 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 180
  (Polychromatic418967fa.accept_16_11_9_4_1_5438 43 105 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 105 180 3 14 35 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 105 180 (Polychromatic418967fa.accept_17_7_3_10_1_2881 41 105 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 105 180 5 8 21 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 105 180 3 13 35 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 105 180
  (Polychromatic418967fa.accept_13_12_1_11_1_1917 38 105 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 105 180 (Polychromatic418967fa.accept_8_5_1_4_1_628 37 105 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 105 180 3 12 35 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 105 180 5 7 21 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 105 180
  (Polychromatic418967fa.accept_13_8_1_11_1_1284 34 105 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 105 180 3 11 35 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 105 180 (Polychromatic418967fa.accept_19_13_10_9_1_5995 32 105 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 180
  (Polychromatic418967fa.accept_19_12_10_9_1_3326 31 105 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 105 180 15 2 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 105 180 (Polychromatic418967fa.accept_8_5_1_4_1_628 29 105 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 180
  (Polychromatic418967fa.accept_16_12_9_4_1_4345 28 105 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 105 180 3 9 35 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 105 180 (Polychromatic418967fa.accept_17_9_3_10_1_9070 26 105 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 105 180 5 5 21 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 105 180 3 8 35 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 105 180
  (Polychromatic418967fa.accept_13_10_1_11_1_1961 23 105 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 105 180 (Polychromatic418967fa.accept_13_9_1_11_1_275 22 105 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 105 180 3 7 35 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 105 180 5 4 21 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 105 180
  (Polychromatic418967fa.accept_14_5_7_12_1_4006 19 105 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 105 180 3 6 35 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 105 180 (Polychromatic418967fa.accept_23_17_13_19_1_10303 17 105 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 180
  (Polychromatic418967fa.accept_13_3_1_11_1_1268 16 105 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 105 180 15 1 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 105 180 (Polychromatic418967fa.accept_16_14_9_4_1_6693 14 105 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 180 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 105 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 105 180 3 4 35 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 105 180
  (Polychromatic418967fa.accept_16_11_9_4_1_5438 11 105 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 105 180 5 2 21 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 105 180 3 3 35 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 105 180 (Polychromatic418967fa.accept_13_8_1_11_1_1284 8 105 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 180 (Polychromatic418967fa.accept_13_7_1_11_1_732 7 105 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 105 180 3 2 35 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 105 180 5 1 21 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 105 180
  (Polychromatic418967fa.accept_19_4_10_9_1_4569 4 105 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 105 180 3 1 35 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 105 180 (Polychromatic418967fa.accept_11_2_6_4_1_3028 2 105 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 180 (Polychromatic418967fa.accept_19_1_10_9_1_10302 1 105
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  180)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 104 180 (Eq.refl
  Bool.true) (allA_succ_of_gcd 76 104 180 4 19 26 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 75 104 180 (Polychromatic418967fa.accept_16_11_8_4_1_2234 75 104 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 104 180 2 37 52 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 104 180 (accept_3_4 73 104 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 104 180 4 18 26 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 104 180
  (Polychromatic418967fa.accept_7_1_6_5_1_39 71 104 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 104 180 2 35 52 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 104 180 (Polychromatic418967fa.accept_14_13_6_12_1_3126 69 104 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 104 180 4 17 26 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 104 180 (accept_3_4 67 104 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 104 180 2 33 52 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 104 180
  (Polychromatic418967fa.accept_11_10_5_4_1_711 65 104 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 104 180 4 16 26 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 104 180 (Polychromatic418967fa.accept_16_15_8_4_1_1355 63 104 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 104 180 2 31 52 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 104 180 (accept_3_4 61 104 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 104 180 4 15 26 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 104 180
  (Polychromatic418967fa.accept_16_11_8_4_1_2234 59 104 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 104 180 2 29 52 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 104 180 (Polychromatic418967fa.accept_7_1_6_5_1_39 57 104 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 104 180 4 14 26 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 104 180 (accept_3_4 55 104 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 104 180 2 27 52 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 104 180 (Polychromatic418967fa.accept_7_4_6_5_1_141 53
  104 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 104 180 4 13 26 45 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 104 180
  (Polychromatic418967fa.accept_16_3_8_4_1_3279 51 104 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 104 180 2 25 52 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 104 180 (accept_3_4 49 104 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 104 180 4 12 26 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 104 180 (Polychromatic418967fa.accept_16_15_8_4_1_1355 47 104 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 104 180 2 23 52 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 104 180
  (Polychromatic418967fa.accept_16_13_8_4_1_3250 45 104 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 104 180 4 11 26 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 104 180 (accept_3_4 43 104 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 104 180 2 21 52 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 104 180 (Polychromatic418967fa.accept_14_13_6_12_1_3126 41 104 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 104 180 4 10 26 45 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 104 180
  (Polychromatic418967fa.accept_7_4_6_5_1_141 39 104 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 104 180 2 19 52 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 104 180 (accept_3_4 37 104 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 104 180 4 9 26 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 104 180 (Polychromatic418967fa.accept_16_3_8_4_1_3279 35 104 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 104 180 2 17 52 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 104 180 (Polychromatic418967fa.accept_16_1_8_4_1_4334
  33 104 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 104 180 4 8 26 45
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 104 180
  (accept_3_4 31 104 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 104 180 2 15 52 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 104 180
  (Polychromatic418967fa.accept_7_1_6_5_1_39 29 104 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 104 180 4 7 26 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 104 180 (Polychromatic418967fa.accept_14_13_6_12_1_3126 27 104 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 104 180 2 13 52 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 104 180 (accept_3_4 25 104 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 104 180 4 6 26 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 104 180 (Polychromatic418967fa.accept_16_7_8_4_1_689
  23 104 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 104 180 2 11 52 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 104 180
  (Polychromatic418967fa.accept_11_10_5_4_1_711 21 104 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 104 180 4 5 26 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 104 180 (accept_3_4 19 104 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  104 180 2 9 52 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  17 104 180 (Polychromatic418967fa.accept_16_1_8_4_1_4334 17 104 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 104 180 4 4 26 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 104 180 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 104 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 104 180 2 7 52 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 104 180 (accept_3_4 13 104 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 104 180 4 3 26 45 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 104 180
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 104 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 104 180 2 5 52 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 104 180 (Polychromatic418967fa.accept_16_9_8_4_1_1354 9 104 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 104 180 4 2 26 45 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 104 180 (accept_3_4 7 104 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 104 180 2 3 52 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 104 180 (Polychromatic418967fa.accept_16_5_8_4_1_5418 5 104 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 104 180 4 1 26 45 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 104 180 (Polychromatic418967fa.accept_16_3_8_4_1_3279 3
  104 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 104 180 2 1 52 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 104 180 (accept_3_4 1
  104 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  180))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 78 103 180 (Eq.refl
  Bool.true) (allA_succ_of_accept 77 103 180 (accept_3_5 77 103 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 103 180 (Polychromatic418967fa.accept_16_12_7_4_1_687 76 103 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 103 180 (Polychromatic418967fa.accept_8_3_7_4_1_42 75 103 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 103 180 (accept_3_5 74 103 180
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 103 180
  (Polychromatic418967fa.accept_14_3_5_12_1_4000 73 103 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 103 180 (Polychromatic418967fa.accept_13_7_12_11_1_1911 72 103 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 103 180 (accept_3_5 71 103 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 103 180 (Polychromatic418967fa.accept_21_7_19_12_1_5579 70 103 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 103 180
  (Polychromatic418967fa.accept_13_4_12_11_1_5362 69 103 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 103 180 (accept_3_5 68 103 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 103 180 (Polychromatic418967fa.accept_8_3_7_4_1_42 67 103 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 103 180 (Polychromatic418967fa.accept_13_1_12_11_1_728 66 103
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 103 180 (accept_3_5 65 103
  180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 103 180
  (Polychromatic418967fa.accept_19_7_8_9_1_7322 64 103 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 103 180 (Polychromatic418967fa.accept_14_7_5_12_1_1439 63 103 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 103 180 (accept_3_5 62 103 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 103 180 (Polychromatic418967fa.accept_16_13_7_4_1_3248 61 103 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 103 180
  (Polychromatic418967fa.accept_16_12_7_4_1_687 60 103 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 103 180 (accept_3_5 59 103 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 103 180 (Polychromatic418967fa.accept_17_7_1_10_1_2836 58 103 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 103 180 (Polychromatic418967fa.accept_21_15_19_12_1_8682 57 103 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 103 180 (accept_3_5 56 103 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 103 180 (Polychromatic418967fa.accept_19_17_8_9_1_10148 55 103
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 103 180
  (Polychromatic418967fa.accept_19_16_8_9_1_8858 54 103 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 103 180 (accept_3_5 53 103 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 103 180 (Polychromatic418967fa.accept_14_10_5_12_1_3995 52 103 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 103 180 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 103 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 103 180 (accept_3_5 50 103 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 103 180 (Polychromatic418967fa.accept_13_10_12_11_1_731 49 103 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 103 180
  (Polychromatic418967fa.accept_17_14_1_10_1_3941 48 103 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 103 180 (accept_3_5 47 103 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 103 180 (Polychromatic418967fa.accept_13_7_12_11_1_1911 46 103 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 103 180
  (Polychromatic418967fa.accept_14_3_5_12_1_4000 45 103 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 103 180 (accept_3_5 44 103 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 103 180 (Polychromatic418967fa.accept_8_3_7_4_1_42 43 103 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 103 180 (Polychromatic418967fa.accept_19_4_8_9_1_10211 42 103 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 103 180 (accept_3_5 41 103 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 103 180 (Polychromatic418967fa.accept_13_1_12_11_1_728 40 103
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 103 180
  (Polychromatic418967fa.accept_19_1_8_9_1_3304 39 103 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 103 180 (accept_3_5 38 103 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 103 180 (Polychromatic418967fa.accept_19_18_8_9_1_3325 37 103 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 103 180 (Polychromatic418967fa.accept_13_10_12_11_1_731 36 103 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 103 180 (accept_3_5 35 103 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 103 180 (Polychromatic418967fa.accept_25_9_3_5_1_10301 34 103
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 103 180
  (Polychromatic418967fa.accept_13_7_12_11_1_1911 33 103 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 103 180 (accept_3_5 32 103 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 103 180 (Polychromatic418967fa.accept_14_3_5_12_1_4000 31 103 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 103 180 (Polychromatic418967fa.accept_13_4_12_11_1_5362 30 103
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 103 180 (accept_3_5 29 103
  180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 103 180
  (Polychromatic418967fa.accept_16_12_7_4_1_687 28 103 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 103 180 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 103 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 103 180 (accept_3_5 26 103 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 103 180 (Polychromatic418967fa.accept_21_4_19_12_1_10195 25 103 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 103 180
  (Polychromatic418967fa.accept_14_10_5_12_1_3995 24 103 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 103 180 (accept_3_5 23 103 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 103 180 (Polychromatic418967fa.accept_21_1_19_12_1_5562 22 103 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 103 180
  (Polychromatic418967fa.accept_14_7_5_12_1_1439 21 103 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 103 180 (accept_3_5 20 103 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 103 180 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 103 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 103 180 (Polychromatic418967fa.accept_19_18_8_9_1_3325 18 103 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 103 180 (accept_3_5 17 103 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 103 180 (Polychromatic418967fa.accept_19_16_8_9_1_8858 16 103
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 103 180
  (Polychromatic418967fa.accept_21_15_19_12_1_8682 15 103 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 103 180 (accept_3_5 14 103 180 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 103 180 (Polychromatic418967fa.accept_16_13_7_4_1_3248 13 103 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 103 180 (Polychromatic418967fa.accept_16_12_7_4_1_687 12 103
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 103 180 (accept_3_5 11 103
  180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 103 180
  (Polychromatic418967fa.accept_13_10_12_11_1_731 10 103 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 103 180 (Polychromatic418967fa.accept_17_9_1_10_1_2859 9 103 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 103 180 (accept_3_5 8 103 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 103 180 (Polychromatic418967fa.accept_13_7_12_11_1_1911 7 103
  180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 103 180
  (Polychromatic418967fa.accept_21_6_19_12_1_3981 6 103 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 103 180 (accept_3_5 5 103 180 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  103 180 (Polychromatic418967fa.accept_13_4_12_11_1_5362 4 103 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 103 180 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 103 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 103 180 (accept_3_5 2 103 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 103 180 (Polychromatic418967fa.accept_13_1_12_11_1_728 1 103 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 103
  180)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 79 102 180 (Eq.refl
  Bool.true) (allA_succ_of_gcd 78 102 180 6 13 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 102 180 (Polychromatic418967fa.accept_16_13_6_4_1_3277 77 102 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 102 180 2 38 51 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 102 180 3 25 34 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 102 180 2 37 51 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 102 180
  (Polychromatic418967fa.accept_11_7_3_4_1_729 73 102 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 102 180 6 12 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 102 180 (Polychromatic418967fa.accept_7_1_4_5_1_35 71 102 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 102 180 2 35 51 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 102 180 3 23 34 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 102 180 2 34 51 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 102 180
  (Polychromatic418967fa.accept_16_3_6_4_1_679 67 102 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 102 180 6 11 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 102 180 (Polychromatic418967fa.accept_7_2_4_5_1_313 65 102 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 102 180 2 32 51 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 102 180 3 21 34 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 102 180 2 31 51 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 102 180
  (Polychromatic418967fa.accept_16_13_6_4_1_3277 61 102 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 102 180 6 10 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 102 180 (Polychromatic418967fa.accept_16_11_6_4_1_2228 59 102 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 102 180 2 29 51 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 102 180 3 19 34 60 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 102 180 2 28 51 90
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 102 180
  (Polychromatic418967fa.accept_7_6_4_5_1_314 55 102 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 102 180 6 9 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 102 180 (Polychromatic418967fa.accept_16_5_6_4_1_3211 53 102 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 102 180 2 26 51 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 102 180 3 17 34 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 102 180 2 25 51 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 102 180
  (Polychromatic418967fa.accept_19_11_7_9_1_8873 49 102 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 102 180 6 8 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 102 180 (Polychromatic418967fa.accept_21_5_18_12_1_5531 47 102 180 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 102 180 2 23 51 90 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 102 180 3 15 34 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 102 180 2 22 51 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 102 180
  (Polychromatic418967fa.accept_7_1_4_5_1_35 43 102 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 102 180 6 7 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 102 180 (Polychromatic418967fa.accept_7_6_4_5_1_314 41 102 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 102 180 2 20 51 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 102 180 3 13 34 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 102 180 2 19 51 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 102 180
  (Polychromatic418967fa.accept_7_2_4_5_1_313 37 102 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 180 6 6 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 102 180 (Polychromatic418967fa.accept_16_3_6_4_1_679 35 102 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 102 180 2 17 51 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 102 180 3 11 34 60 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 102 180 2 16 51 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 102 180
  (Polychromatic418967fa.accept_24_7_6_12_1_10300 31 102 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 102 180 6 5 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 102 180 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 102 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 102 180 2 14 51 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 102 180 3 9 34 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 102 180 2 13 51 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 102 180
  (Polychromatic418967fa.accept_21_4_18_12_1_5532 25 102 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 102 180 6 4 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 102 180 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 102 180 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 102 180 2 11 51 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 102 180 3 7 34 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 102 180 2 10 51 90 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 102 180
  (Polychromatic418967fa.accept_16_3_6_4_1_679 19 102 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 180 6 3 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 102 180 (Polychromatic418967fa.accept_19_17_7_9_1_3324 17 102 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 102 180 2 8 51 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 102 180 3 5 34 60 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 102 180 2 7 51 90 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 102 180 (Polychromatic418967fa.accept_7_6_4_5_1_314 13
  102 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 102 180 6 2 17 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 102 180
  (Polychromatic418967fa.accept_16_11_6_4_1_2228 11 102 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 102 180 2 5 51 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 102 180 3 3 34 60 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 102 180 2 4 51 90 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 102 180 (Polychromatic418967fa.accept_11_7_3_4_1_729 7 102 180 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102 180 6 1 17 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 102 180 (Polychromatic418967fa.accept_16_5_6_4_1_3211 5 102 180
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 102 180 2 2 51 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 102 180 3 1 34 60 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 102 180 2 1 51 90 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 180
  (Polychromatic418967fa.accept_7_1_4_5_1_35 1 102 180 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 102 180)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_180_segment_000))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


