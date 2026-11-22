-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch182
-- name    : Polychromatic418967fa_Branch182
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:19:19.619005+00:00
-- url     : https://prove2.me/theorems/a83ce95c-6090-4fa2-9344-15ef95a5be8c
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch182_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_182 : allB 182 182 :=
  allB_succ' 2 181 182 (Eq.refl Bool.true) (allA_of_3_0 2 181 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  180 182 (Eq.refl Bool.true) (allA_succ_of_gcd 2 180 182 2 1 90 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 180 182 (accept_3_2 1 180 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 180 182))) (allB_succ' 4 179 182 (Eq.refl Bool.true) (allA_succ_of_accept 3 179 182
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 179 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 179 182 (Polychromatic418967fa.accept_16_2_3_6_1_3372 2 179 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 179 182 (accept_3_2 1 179 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 179 182)))) (allB_succ' 5 178 182 (Eq.refl Bool.true) (allA_of_3_0 5 178 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 6 177 182 (Eq.refl Bool.true) (allA_succ_of_accept 5 177 182
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 177 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 177 182 (accept_3_2 4 177 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  177 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 177 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 177 182 (Polychromatic418967fa.accept_16_2_1_6_1_2342 2 177 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 182 (accept_3_2 1 177 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 177 182)))))) (allB_succ' 7 176 182 (Eq.refl Bool.true) (allA_succ_of_gcd 6 176 182 2 3
  88 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 176 182
  (Polychromatic418967fa.accept_12_5_8_2_1_309 5 176 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 176 182 2 2 88 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 176 182 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 176 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 176 182 2 1 88 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 176 182 (accept_3_2 1 176 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 176 182))))))) (allB_succ' 8 175 182 (Eq.refl Bool.true) (allA_of_3_0 8 175 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 9 174 182 (Eq.refl Bool.true) (allA_succ_of_gcd 8 174 182 2 4 87 91
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 174 182
  (accept_3_2 7 174 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 174 182 2 3 87 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 174 182
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 174 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 174 182 2 2 87 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 174 182 (Polychromatic418967fa.accept_11_3_9_6_1_105 3 174 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 174 182 2 1 87 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 174 182 (accept_3_2 1 174 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 174 182))))))))) (allB_succ' 10 173 182 (Eq.refl Bool.true) (allA_succ_of_accept 9 173 182
  (Polychromatic418967fa.accept_6_3_5_2_1_12 9 173 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 173 182 (Polychromatic418967fa.accept_12_8_5_2_1_746 8 173 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 173 182 (accept_3_2 7 173 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 173 182 (Polychromatic418967fa.accept_15_6_8_2_1_104 6 173 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 173 182 (Polychromatic418967fa.accept_10_5_3_2_1_899 5
  173 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 173 182 (accept_3_2 4 173
  182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 173 182 (Polychromatic418967fa.accept_4_3_1_2_1_62
  3 173 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 173 182
  (Polychromatic418967fa.accept_22_2_19_6_1_5421 2 173 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 173 182 (accept_3_2 1 173 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 173
  182)))))))))) (allB_succ' 11 172 182 (Eq.refl Bool.true) (allA_of_3_0 11 172 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 171 182 (Eq.refl Bool.true) (allA_succ_of_accept 11 171 182
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 171 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 171 182 (accept_3_2 10 171 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  171 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 171 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 171 182 (Polychromatic418967fa.accept_15_8_6_2_1_1128 8 171 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 182 (accept_3_2 7 171 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 171 182 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 171 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 171 182
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 171 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 171 182 (accept_3_2 4 171 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  171 182 (Polychromatic418967fa.accept_10_3_1_2_1_521 3 171 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 171 182 (Polychromatic418967fa.accept_16_2_11_6_1_737 2 171 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 182 (accept_3_2 1 171 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 171 182)))))))))))) (allB_succ' 13 170 182 (Eq.refl Bool.true) (allA_succ_of_gcd 12 170
  182 2 6 85 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  170 182 (Polychromatic418967fa.accept_15_11_5_2_1_520 11 170 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 170 182 2 5 85 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 170 182 (Polychromatic418967fa.accept_21_9_2_14_1_7251 9 170 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 170 182 2 4 85 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 170 182 (accept_3_2 7 170 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 170 182 2 3 85 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 170 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 170 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 170 182 2 2 85 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 170 182
  (Polychromatic418967fa.accept_9_3_8_2_1_162 3 170 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 170 182 2 1 85 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 170 182 (accept_3_2 1 170 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 170
  182))))))))))))) (allB_succ' 14 169 182 (Eq.refl Bool.true) (allA_of_3_0 14 169 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 168 182 (Eq.refl Bool.true) (allA_succ_of_gcd 14 168 182 14 1 12 13 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 168 182 (accept_3_2 13 168 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 168 182 2 6 84 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 168 182
  (Polychromatic418967fa.accept_25_11_18_7_1_10524 11 168 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 168 182 2 5 84 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 168 182 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 168 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 168 182 2 4 84 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 168 182 7 1 24 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 168 182 2 3 84 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 168 182
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 168 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 168 182 2 2 84 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 168 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 168 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 168 182 2 1 84 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 168 182 (accept_3_2 1 168 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 168 182))))))))))))))) (allB_succ' 16 167 182 (Eq.refl Bool.true) (allA_succ_of_accept 15 167
  182 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 167 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 167 182 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 167 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 167 182 (accept_3_2 13 167 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 167 182 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 167 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 167 182
  (Polychromatic418967fa.accept_17_11_14_12_1_2995 11 167 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 167 182 (accept_3_2 10 167 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 167 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 167 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 167 182 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 167 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 167 182 (accept_3_2 7 167 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 167 182 (Polychromatic418967fa.accept_9_6_5_2_1_421 6
  167 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 167 182
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 167 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 167 182 (accept_3_2 4 167 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  167 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 167 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 167 182 (Polychromatic418967fa.accept_19_2_15_11_1_7497 2 167 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 167 182 (accept_3_2 1 167 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 167 182)))))))))))))))) (allB_succ' 17 166 182 (Eq.refl Bool.true)
  (allA_of_3_0 17 166 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 18 165 182 (Eq.refl Bool.true)
  (allA_succ_of_accept 17 165 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 165 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 165 182 (accept_3_2 16 165 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 165 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 165 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 165 182 (Polychromatic418967fa.accept_9_5_3_2_1_171
  14 165 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 165 182 (accept_3_2 13
  165 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 165 182
  (Polychromatic418967fa.accept_18_12_3_2_1_756 12 165 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 165 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 165 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 165 182 (accept_3_2 10 165 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 165 182 (Polychromatic418967fa.accept_18_9_3_2_1_3814 9 165 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 165 182 (Polychromatic418967fa.accept_9_8_3_2_1_417 8
  165 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 182 (accept_3_2 7 165
  182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 165 182
  (Polychromatic418967fa.accept_9_6_3_2_1_431 6 165 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 165 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 165 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 165 182 (accept_3_2 4 165 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 165 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 165 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 165 182
  (Polychromatic418967fa.accept_19_2_13_11_1_10497 2 165 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 165 182 (accept_3_2 1 165 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one
  165 182)))))))))))))))))) (allB_succ' 19 164 182 (Eq.refl Bool.true) (allA_succ_of_gcd 18 164 182 2 9 82 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 164 182
  (Polychromatic418967fa.accept_10_7_4_2_1_903 17 164 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 164 182 2 8 82 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 164 182 (Polychromatic418967fa.accept_20_15_4_2_1_5914 15 164 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 164 182 2 7 82 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 164 182 (accept_3_2 13 164 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 164 182 2 6 82 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 164 182 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 164
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 164 182 2 5 82 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 164 182
  (Polychromatic418967fa.accept_20_9_4_2_1_1900 9 164 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 164 182 2 4 82 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 164 182 (accept_3_2 7 164 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 164
  182 2 3 82 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  164 182 (Polychromatic418967fa.accept_11_5_10_6_1_793 5 164 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 164 182 2 2 82 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 164 182 (Polychromatic418967fa.accept_15_3_14_2_1_1888 3 164 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 164 182 2 1 82 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 164 182 (accept_3_2 1 164 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 164 182))))))))))))))))))) (allB_succ' 20 163 182 (Eq.refl Bool.true) (allA_of_3_0 20
  163 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 21 162 182 (Eq.refl Bool.true) (allA_succ_of_gcd 20 162
  182 2 10 81 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19
  162 182 (accept_3_2 19 162 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 162 182 2 9 81 91
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 162 182
  (Polychromatic418967fa.accept_16_1_2_6_1_2295 17 162 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 162 182 2 8 81 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 162 182 (Polychromatic418967fa.accept_12_3_6_2_1_747 15 162 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 162 182 2 7 81 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 162 182 (accept_3_2 13 162 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 162 182 2 6 81 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 162 182 (Polychromatic418967fa.accept_16_11_2_6_1_1435 11 162
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 162 182 2 5 81 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 162 182
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 162 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 162 182 2 4 81 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 162 182 (accept_3_2 7 162 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 162
  182 2 3 81 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  162 182 (Polychromatic418967fa.accept_15_5_12_2_1_2820 5 162 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 162 182 2 2 81 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 162 182 (Polychromatic418967fa.accept_11_3_8_6_1_788 3 162 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 162 182 2 1 81 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 162 182 (accept_3_2 1 162 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 162 182))))))))))))))))))))) (allB_succ' 22 161 182 (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 161 182 7 3 23 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 161 182 (Polychromatic418967fa.accept_12_8_5_2_1_746 20 161 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 161 182 (accept_3_2 19 161 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 161 182 (Polychromatic418967fa.accept_16_2_1_6_1_2342 18 161 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 161 182
  (Polychromatic418967fa.accept_19_17_9_11_1_6057 17 161 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 161 182 (accept_3_2 16 161 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 161 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 161 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 161 182 7 2 23 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 161 182 (accept_3_2 13 161 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 161 182 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 161 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 161 182
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 161 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 161 182 (accept_3_2 10 161 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  161 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 161 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 161 182 (Polychromatic418967fa.accept_12_8_5_2_1_746 8 161 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 161 182 7 1 23 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 161 182 (Polychromatic418967fa.accept_9_6_8_2_1_410 6
  161 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 161 182
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 161 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 161 182 (accept_3_2 4 161 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  161 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 161 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 161 182 (Polychromatic418967fa.accept_16_2_1_6_1_2342 2 161 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 161 182 (accept_3_2 1 161 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 161 182)))))))))))))))))))))) (allB_succ' 23 160 182 (Eq.refl Bool.true) (allA_of_3_0
  23 160 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 159 182 (Eq.refl Bool.true) (allA_succ_of_accept 23
  159 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 159 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 159 182 (accept_3_2 22 159 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 159 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 159 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 159 182 (Polychromatic418967fa.accept_28_20_19_14_1_10523 20
  159 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 159 182 (accept_3_2 19
  159 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 159 182
  (Polychromatic418967fa.accept_12_6_3_2_1_743 18 159 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 159 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 159 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 159 182 (accept_3_2 16 159 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 159 182 (Polychromatic418967fa.accept_19_15_7_11_1_7657 15 159 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 159 182
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 159 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 159 182 (accept_3_2 13 159 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 159 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 159 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 159 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 159 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 159 182 (accept_3_2 10 159 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 159 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 159 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 159 182
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 159 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 159 182 (accept_3_2 7 159 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  159 182 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 159 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 159 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 159 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 159 182 (accept_3_2 4 159 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 159 182 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 159 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 159 182
  (Polychromatic418967fa.accept_17_2_6_12_1_7912 2 159 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 159 182 (accept_3_2 1 159 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 159
  182)))))))))))))))))))))))) (allB_succ' 25 158 182 (Eq.refl Bool.true) (allA_succ_of_gcd 24 158 182 2 12 79 91
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 158 182
  (Polychromatic418967fa.accept_20_3_18_2_1_5918 23 158 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 158 182 2 11 79 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 158 182 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 158 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 158 182 2 10 79 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 158 182 (accept_3_2 19 158 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 158 182 2 9 79 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 158 182 (Polychromatic418967fa.accept_9_8_5_2_1_422 17
  158 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 158 182 2 8 79 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 158 182
  (Polychromatic418967fa.accept_9_6_5_2_1_421 15 158 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 158 182 2 7 79 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 158 182 (accept_3_2 13 158 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12
  158 182 2 6 79 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  11 158 182 (Polychromatic418967fa.accept_18_11_14_2_1_5058 11 158 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 158 182 2 5 79 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 158 182 (Polychromatic418967fa.accept_15_9_8_2_1_1109 9 158 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 158 182 2 4 79 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 158 182 (accept_3_2 7 158 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 158 182 2 3 79 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 158 182 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 158 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 158 182 2 2 79 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 158 182
  (Polychromatic418967fa.accept_9_3_5_2_1_28 3 158 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 158 182 2 1 79 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 158 182 (accept_3_2 1 158 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158
  182))))))))))))))))))))))))) (allB_succ' 26 157 182 (Eq.refl Bool.true) (allA_of_3_0 26 157 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 27 156 182 (Eq.refl Bool.true) (allA_succ_of_gcd 26 156 182 26 1 6 7 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 156 182 (accept_3_2 25
  156 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 156 182 2 12 78 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 156 182
  (Polychromatic418967fa.accept_9_5_3_2_1_171 23 156 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 156 182 2 11 78 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 156 182 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 156 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 156 182 2 10 78 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 156 182 (accept_3_2 19 156 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 156 182 2 9 78 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 156 182 (Polychromatic418967fa.accept_9_8_3_2_1_417 17
  156 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 156 182 2 8 78 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 156 182
  (Polychromatic418967fa.accept_9_6_3_2_1_431 15 156 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 156 182 2 7 78 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 13 156 182 13 1 12 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 12 156 182 2 6 78 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 156 182 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 156 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 156 182 2 5 78 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 156 182
  (Polychromatic418967fa.accept_25_9_6_7_1_10522 9 156 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 156 182 2 4 78 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 156 182 (accept_3_2 7 156 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 156
  182 2 3 78 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  156 182 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 156 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 156 182 2 2 78 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 156 182 (Polychromatic418967fa.accept_18_3_12_2_1_2639 3 156 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 156 182 2 1 78 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 156 182 (accept_3_2 1 156 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 156 182))))))))))))))))))))))))))) (allB_succ' 28 155 182 (Eq.refl Bool.true)
  (allA_succ_of_accept 27 155 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 155 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 155 182 (Polychromatic418967fa.accept_15_11_5_2_1_520 26 155
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 155 182 (accept_3_2 25 155
  182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 155 182
  (Polychromatic418967fa.accept_17_7_2_12_1_1069 24 155 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 155 182 (Polychromatic418967fa.accept_10_3_5_2_1_38 23 155 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 155 182 (accept_3_2 22 155 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 155 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 155 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 155 182
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 155 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 155 182 (accept_3_2 19 155 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 155 182 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 155 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 155 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 155 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 155 182 (accept_3_2 16 155 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 155 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 155 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 155 182
  (Polychromatic418967fa.accept_15_14_5_2_1_4761 14 155 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 155 182 (accept_3_2 13 155 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 155 182 (Polychromatic418967fa.accept_15_12_5_2_1_2786 12 155 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 155 182 (Polychromatic418967fa.accept_15_11_5_2_1_520 11 155 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 155 182 (accept_3_2 10 155 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 155 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 155 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 155 182
  (Polychromatic418967fa.accept_10_8_5_2_1_881 8 155 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 155 182 (accept_3_2 7 155 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  155 182 (Polychromatic418967fa.accept_17_6_2_12_1_1992 6 155 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 155 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 155 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 155 182 (accept_3_2 4 155 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 155 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 155 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 155 182
  (Polychromatic418967fa.accept_16_2_11_6_1_737 2 155 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 155 182 (accept_3_2 1 155 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 155
  182)))))))))))))))))))))))))))) (allB_succ' 29 154 182 (Eq.refl Bool.true) (allA_of_3_0 29 154 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 30 153 182 (Eq.refl Bool.true) (allA_succ_of_accept 29 153 182
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 153 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 153 182 (accept_3_2 28 153 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 153 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 153 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 153 182 (Polychromatic418967fa.accept_31_26_29_27_1_10521 26 153 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 153 182 (accept_3_2 25 153 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 153 182 (Polychromatic418967fa.accept_18_6_9_2_1_1575 24 153
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 153 182
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 153 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 153 182 (accept_3_2 22 153 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 153 182 (Polychromatic418967fa.accept_10_1_3_2_1_220 21 153 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 153 182 (Polychromatic418967fa.accept_15_5_3_2_1_5930 20 153 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 182 (accept_3_2 19 153 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 153 182 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 153
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 153 182
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 153 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 153 182 (accept_3_2 16 153 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 153 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 153 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 153 182 (Polychromatic418967fa.accept_15_14_3_2_1_2811 14 153 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 182 (accept_3_2 13 153 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 153 182 (Polychromatic418967fa.accept_15_12_3_2_1_2756 12 153
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 153 182
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 153 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 153 182 (accept_3_2 10 153 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  153 182 (Polychromatic418967fa.accept_19_9_1_11_1_7643 9 153 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 153 182 (Polychromatic418967fa.accept_19_8_1_11_1_4718 8 153 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 182 (accept_3_2 7 153 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 153 182 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 153 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 153 182
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 153 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 153 182 (accept_3_2 4 153 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  153 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 153 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 153 182 (Polychromatic418967fa.accept_16_2_9_6_1_4441 2 153 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 182 (accept_3_2 1 153 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 153 182)))))))))))))))))))))))))))))) (allB_succ' 31 152 182 (Eq.refl Bool.true)
  (allA_succ_of_gcd 30 152 182 2 15 76 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 152 182 (Polychromatic418967fa.accept_12_5_8_2_1_309 29 152 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 152 182 2 14 76 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 152 182
  (Polychromatic418967fa.accept_20_7_12_2_1_4465 27 152 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 152 182 2 13 76 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 152 182 (accept_3_2 25 152 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 152 182 2 12 76 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 152 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 152 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 152 182 2 11 76 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 152 182
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 152 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 152 182 2 10 76 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 152 182 (accept_3_2 19 152 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 152 182 2 9 76 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 152 182 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 152 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 152 182 2 8 76 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 152 182 (Polychromatic418967fa.accept_9_6_8_2_1_410 15
  152 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 152 182 2 7 76 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 152 182 (accept_3_2 13
  152 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 152 182 2 6 76 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 152 182
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 152 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 152 182 2 5 76 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 152 182 (Polychromatic418967fa.accept_20_9_12_2_1_5935 9 152 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 152 182 2 4 76 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 152 182 (accept_3_2 7 152 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 152 182 2 3 76 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 152 182 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 152 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 152 182 2 2 76 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 152 182 (Polychromatic418967fa.accept_9_3_8_2_1_162 3
  152 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 152 182 2 1 76 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 152 182 (accept_3_2 1
  152 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152 182))))))))))))))))))))))))))))))) (allB_succ' 32 151
  182 (Eq.refl Bool.true) (allA_of_3_0 32 151 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 150 182
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 150 182 2 16 75 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 150 182 (accept_3_2 31 150 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 150 182 2 15 75 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 150 182 (Polychromatic418967fa.accept_21_8_3_14_1_4165 29 150 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 150 182 2 14 75 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 150 182
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 150 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 150 182 2 13 75 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 150 182 (accept_3_2 25 150 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 150 182 2 12 75 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 150 182 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 150 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 150 182 2 11 75 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 150 182
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 150 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 150 182 2 10 75 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 150 182 (accept_3_2 19 150 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 150 182 2 9 75 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 150 182 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 150 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 150 182 2 8 75 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 150 182 (Polychromatic418967fa.accept_12_3_6_2_1_747
  15 150 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 150 182 2 7 75 91
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 150 182
  (accept_3_2 13 150 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 150 182 2 6 75 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 150 182
  (Polychromatic418967fa.accept_17_11_14_12_1_2995 11 150 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 150 182 2 5 75 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 150 182 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 150 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 150 182 2 4 75 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 150 182 (accept_3_2 7 150 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 150 182 2 3 75 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 150 182 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 150 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 150 182 2 2 75 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 150 182
  (Polychromatic418967fa.accept_9_3_6_2_1_160 3 150 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 150 182 2 1 75 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 150 182 (accept_3_2 1 150 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  182))))))))))))))))))))))))))))))))) (allB_succ' 34 149 182 (Eq.refl Bool.true) (allA_succ_of_accept 33 149 182
  (Polychromatic418967fa.accept_6_3_5_2_1_12 33 149 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 149 182 (Polychromatic418967fa.accept_12_8_5_2_1_746 32 149 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 149 182 (accept_3_2 31 149 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 149 182 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 149 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 149 182
  (Polychromatic418967fa.accept_21_8_2_14_1_10496 29 149 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 149 182 (accept_3_2 28 149 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 149 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 149 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 149 182 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 149 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 149 182 (accept_3_2 25 149 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 149 182 (Polychromatic418967fa.accept_9_6_5_2_1_421
  24 149 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 149 182
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 149 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 149 182 (accept_3_2 22 149 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 149 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 149 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 149 182 (Polychromatic418967fa.accept_12_8_5_2_1_746 20 149 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 149 182 (accept_3_2 19 149 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 149 182 (Polychromatic418967fa.accept_15_3_14_2_1_1888 18 149
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 149 182
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 149 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 149 182 (accept_3_2 16 149 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 149 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 149 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 149 182 (Polychromatic418967fa.accept_19_14_16_11_1_9054 14 149 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 149 182 (accept_3_2 13 149 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 149 182 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 149 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 149 182
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 149 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 149 182 (accept_3_2 10 149 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  149 182 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 149 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 149 182 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 149 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 149 182 (accept_3_2 7 149 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 149 182 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 149 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 149 182
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 5 149 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 149 182 (accept_3_2 4 149 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  149 182 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 149 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 149 182 (Polychromatic418967fa.accept_19_2_16_11_1_6045 2 149 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 149 182 (accept_3_2 1 149 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 149 182)))))))))))))))))))))))))))))))))) (allB_succ' 35 148 182 (Eq.refl
  Bool.true) (allA_of_3_0 35 148 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 147 182 (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 147 182 7 5 21 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 147 182 (accept_3_2 34 147 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 147 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 147 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 147 182 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 147 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 147 182 (accept_3_2 31 147 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 147 182 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 147 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 147 182
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 147 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 147 182 7 4 21 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 147 182 (Polychromatic418967fa.accept_16_11_3_6_1_4462 27 147 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 147 182 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 147 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 147 182 (accept_3_2 25 147 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 147 182 (Polychromatic418967fa.accept_9_6_3_2_1_431
  24 147 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 147 182
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 147 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 147 182 (accept_3_2 22 147 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21
  147 182 7 3 21 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  20 147 182 (Polychromatic418967fa.accept_15_5_12_2_1_2820 20 147 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 147 182 (accept_3_2 19 147 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 147 182 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 147 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 147 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 147 182
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 147 182 (accept_3_2 16 147 182
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 147 182 (Polychromatic418967fa.accept_9_6_3_2_1_431
  15 147 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 147 182 7 2 21 26
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 147 182
  (accept_3_2 13 147 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 147 182
  (Polychromatic418967fa.accept_18_12_3_2_1_756 12 147 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 147 182 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 147 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 147 182 (accept_3_2 10 147 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 147 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 147 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 147 182 (Polychromatic418967fa.accept_9_8_3_2_1_417 8
  147 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 147 182 7 1 21 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 147 182
  (Polychromatic418967fa.accept_9_6_3_2_1_431 6 147 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 147 182 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 147 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 147 182 (accept_3_2 4 147 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 147 182 (Polychromatic418967fa.accept_15_3_12_2_1_507 3 147 182 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 147 182 (Polychromatic418967fa.accept_11_2_4_6_1_2412
  2 147 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 182 (accept_3_2 1
  147 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 147 182)))))))))))))))))))))))))))))))))))) (allB_succ' 37
  146 182 (Eq.refl Bool.true) (allA_succ_of_gcd 36 146 182 2 18 73 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 146 182 (Polychromatic418967fa.accept_15_5_11_2_1_1095 35 146
  182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 146 182 2 17 73 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 146 182
  (Polychromatic418967fa.accept_16_1_2_6_1_2295 33 146 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 146 182 2 16 73 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 146 182 (accept_3_2 31 146 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 146 182 2 15 73 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 146 182 (Polychromatic418967fa.accept_23_6_8_21_1_10520 29 146 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 146 182 2 14 73 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 146 182
  (Polychromatic418967fa.accept_16_11_2_6_1_1435 27 146 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 146 182 2 13 73 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 146 182 (accept_3_2 25 146 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 146 182 2 12 73 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 146 182 (Polychromatic418967fa.accept_17_6_10_12_1_4129 23 146 182 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 146 182 2 11 73 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 146 182
  (Polychromatic418967fa.accept_10_1_6_2_1_867 21 146 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 146 182 2 10 73 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 146 182 (accept_3_2 19 146 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 146 182 2 9 73 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 146 182 (Polychromatic418967fa.accept_16_1_2_6_1_2295 17 146 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 146 182 2 8 73 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 146 182
  (Polychromatic418967fa.accept_21_15_20_14_1_10519 15 146 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 146 182 2 7 73 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 146 182 (accept_3_2 13 146 182 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 146 182 2 6 73 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 146 182 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 146 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 146 182 2 5 73 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 146 182 (Polychromatic418967fa.accept_11_9_3_6_1_797 9
  146 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 146 182 2 4 73 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 146 182 (accept_3_2 7
  146 182 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 146 182 2 3 73 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 146 182
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 5 146 182 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 146 182 2 2 73 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 146 182 (Polychromatic418967fa.accept_16_3_2_6_1_4461 3 146 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 146 182 2 1 73 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 146 182 (accept_3_2 1 146 182 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 146 182)))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_182_segment_000))))))))))))))))))))))))))))))))))))


