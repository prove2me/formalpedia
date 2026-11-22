-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch173
-- name    : Polychromatic418967fa_Branch173
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:19:30.30928+00:00
-- url     : https://prove2.me/theorems/49e7165d-ee2f-4a29-a104-cf4c94dad13f
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

def Polychromatic418967fa.branch_173 : allB 173 173 :=
  allB_succ' 2 172 173 (Eq.refl Bool.true) (allA_of_3_0 2 172 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  171 173 (Eq.refl Bool.true) (allA_succ_of_accept 2 171 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 171 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 173 (accept_3_2 1 171 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 171 173))) (allB_succ' 4 170 173 (Eq.refl Bool.true)
  (allA_succ_of_accept 3 170 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 170 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 170 173 (Polychromatic418967fa.accept_11_2_5_8_1_470 2 170 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 170 173 (accept_3_2 1 170 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 170 173)))) (allB_succ' 5 169 173 (Eq.refl Bool.true) (allA_of_3_0
  5 169 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 6 168 173 (Eq.refl Bool.true) (allA_succ_of_accept 5
  168 173 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 168 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 168 173 (accept_3_2 4 168 173 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 168 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 168 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 168 173 (Polychromatic418967fa.accept_13_2_12_4_1_943 2 168 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 168 173 (accept_3_2 1 168 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 168 173)))))) (allB_succ' 7 167 173 (Eq.refl Bool.true)
  (allA_succ_of_accept 6 167 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 167 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 167 173 (Polychromatic418967fa.accept_10_5_7_3_1_561 5 167 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 167 173 (accept_3_2 4 167 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 167 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 3
  167 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 167 173
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 167 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 167 173 (accept_3_2 1 167 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 167 173)))))))
  (allB_succ' 8 166 173 (Eq.refl Bool.true) (allA_of_3_0 8 166 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  9 165 173 (Eq.refl Bool.true) (allA_succ_of_accept 8 165 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 165 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 173 (accept_3_2 7 165 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 165 173 (Polychromatic418967fa.accept_7_6_4_5_1_314 6
  165 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 165 173
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 165 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 165 173 (accept_3_2 4 165 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  165 173 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 165 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 165 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 165 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 173 (accept_3_2 1 165 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 165 173))))))))) (allB_succ' 10 164 173 (Eq.refl Bool.true) (allA_succ_of_accept 9 164
  173 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 164 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 164 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 164 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 164 173 (accept_3_2 7 164 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 164 173 (Polychromatic418967fa.accept_15_6_14_8_1_245 6 164 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 164 173 (Polychromatic418967fa.accept_15_5_14_8_1_1376
  5 164 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 164 173 (accept_3_2 4
  164 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 164 173
  (Polychromatic418967fa.accept_6_3_2_5_1_32 3 164 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 164 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 164 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 164 173 (accept_3_2 1 164 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 164 173)))))))))) (allB_succ' 11 163 173 (Eq.refl Bool.true) (allA_of_3_0 11 163 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 12 162 173 (Eq.refl Bool.true) (allA_succ_of_accept 11 162 173
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 162 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 162 173 (accept_3_2 10 162 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  162 173 (Polychromatic418967fa.accept_13_9_6_4_1_2243 9 162 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 162 173 (Polychromatic418967fa.accept_19_8_10_2_1_5414 8 162 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 162 173 (accept_3_2 7 162 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 162 173 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 162 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 162 173
  (Polychromatic418967fa.accept_10_5_2_3_1_239 5 162 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 162 173 (accept_3_2 4 162 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  162 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 162 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 162 173 (Polychromatic418967fa.accept_13_2_6_4_1_1593 2 162 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 162 173 (accept_3_2 1 162 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 162 173)))))))))))) (allB_succ' 13 161 173 (Eq.refl Bool.true) (allA_succ_of_accept 12
  161 173 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 161 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 161 173 (Polychromatic418967fa.accept_19_11_9_2_1_1729 11 161 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 161 173 (accept_3_2 10 161 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 161 173 (Polychromatic418967fa.accept_13_9_5_4_1_1591 9 161 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 161 173
  (Polychromatic418967fa.accept_10_8_1_3_1_1374 8 161 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 161 173 (accept_3_2 7 161 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  161 173 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 161 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 161 173 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 161 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 161 173 (accept_3_2 4 161 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 161 173 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 161 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 161 173
  (Polychromatic418967fa.accept_10_2_1_3_1_233 2 161 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 161 173 (accept_3_2 1 161 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 161
  173))))))))))))) (allB_succ' 14 160 173 (Eq.refl Bool.true) (allA_of_3_0 14 160 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 159 173 (Eq.refl Bool.true) (allA_succ_of_accept 14 159 173
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 159 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 159 173 (accept_3_2 13 159 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 159 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 159 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 159 173 (Polychromatic418967fa.accept_21_11_12_5_1_2224 11 159 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 159 173 (accept_3_2 10 159 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 159 173 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 159 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 159 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 159 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 159 173 (accept_3_2 7 159 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  159 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 159 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 159 173 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 159 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 159 173 (accept_3_2 4 159 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 159 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 159 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 159 173
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 159 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 159 173 (accept_3_2 1 159 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 159
  173))))))))))))))) (allB_succ' 16 158 173 (Eq.refl Bool.true) (allA_succ_of_accept 15 158 173
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 158 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 158 173 (Polychromatic418967fa.accept_21_14_11_5_1_6591 14 158 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 158 173 (accept_3_2 13 158 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 158 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 158 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 158 173
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 158 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 158 173 (accept_3_2 10 158 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  158 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 158 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 158 173 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 158 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 158 173 (accept_3_2 7 158 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 158 173 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 158 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 158 173
  (Polychromatic418967fa.accept_10_5_8_3_1_229 5 158 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 158 173 (accept_3_2 4 158 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  158 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 158 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 158 173 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 158 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 158 173 (accept_3_2 1 158 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 158 173)))))))))))))))) (allB_succ' 17 157 173 (Eq.refl Bool.true) (allA_of_3_0 17 157
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 18 156 173 (Eq.refl Bool.true) (allA_succ_of_accept 17 156
  173 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 156 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 156 173 (accept_3_2 16 156 173 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 156 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 156 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 156 173 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 156 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 156 173 (accept_3_2 13 156 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 156 173
  (Polychromatic418967fa.accept_19_12_4_2_1_4121 12 156 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 156 173 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 156 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 156 173 (accept_3_2 10 156 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 156 173 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 156 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 156 173 (Polychromatic418967fa.accept_9_8_3_2_1_417 8
  156 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 156 173 (accept_3_2 7 156
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 156 173
  (Polychromatic418967fa.accept_9_6_3_2_1_431 6 156 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 156 173 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 156 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 156 173 (accept_3_2 4 156 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 156 173 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 156 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 156 173 (Polychromatic418967fa.accept_15_2_6_8_1_754 2
  156 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 156 173 (accept_3_2 1 156
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156 173)))))))))))))))))) (allB_succ' 19 155 173 (Eq.refl
  Bool.true) (allA_succ_of_accept 18 155 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 155 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 155 173 (Polychromatic418967fa.accept_7_3_1_5_1_44 17
  155 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 155 173 (accept_3_2 16
  155 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 155 173
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 15 155 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 155 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 155 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 155 173 (accept_3_2 13 155 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 155 173 (Polychromatic418967fa.accept_10_2_5_3_1_1408 12 155 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 155 173
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 155 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 155 173 (accept_3_2 10 155 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  155 173 (Polychromatic418967fa.accept_27_9_20_11_1_5703 9 155 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 155 173 (Polychromatic418967fa.accept_10_8_5_3_1_543 8 155 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 155 173 (accept_3_2 7 155 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 155 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 155 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 155 173
  (Polychromatic418967fa.accept_13_5_12_4_1_449 5 155 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 155 173 (accept_3_2 4 155 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  155 173 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 155 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 155 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 155 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 155 173 (accept_3_2 1 155 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 155 173))))))))))))))))))) (allB_succ' 20 154 173 (Eq.refl Bool.true) (allA_of_3_0 20
  154 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 21 153 173 (Eq.refl Bool.true) (allA_succ_of_accept 20
  153 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 153 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 153 173 (accept_3_2 19 153 173 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 153 173 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 153 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 153 173 (Polychromatic418967fa.accept_16_1_9_13_1_1822 17 153
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 153 173 (accept_3_2 16 153
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 153 173
  (Polychromatic418967fa.accept_7_1_6_5_1_39 15 153 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 153 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 153 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 173 (accept_3_2 13 153 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 153 173 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 153 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 153 173 (Polychromatic418967fa.accept_7_4_6_5_1_141
  11 153 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 153 173 (accept_3_2 10
  153 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 153 173
  (Polychromatic418967fa.accept_11_9_10_8_1_444 9 153 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 153 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 153 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 173 (accept_3_2 7 153 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 153 173 (Polychromatic418967fa.accept_13_6_10_4_1_957 6 153 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 153 173 (Polychromatic418967fa.accept_13_5_10_4_1_1564
  5 153 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 173 (accept_3_2 4
  153 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 153 173
  (Polychromatic418967fa.accept_12_3_9_5_1_853 3 153 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 153 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 153 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 173 (accept_3_2 1 153 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 153 173))))))))))))))))))))) (allB_succ' 22 152 173 (Eq.refl Bool.true) (allA_succ_of_accept 21
  152 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 152 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 152 173 (Polychromatic418967fa.accept_13_7_9_4_1_918 20 152 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 152 173 (accept_3_2 19 152 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 152 173 (Polychromatic418967fa.accept_13_5_9_4_1_441 18 152
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 152 173
  (Polychromatic418967fa.accept_14_3_12_5_1_153 17 152 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 152 173 (accept_3_2 16 152 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 152 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 152 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 152 173 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 152 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 152 173 (accept_3_2 13 152 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 152 173 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 152 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 152 173
  (Polychromatic418967fa.accept_10_1_2_3_1_1910 11 152 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 152 173 (accept_3_2 10 152 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  152 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 152 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 152 173 (Polychromatic418967fa.accept_13_8_9_4_1_1552 8 152 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 152 173 (accept_3_2 7 152 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 152 173 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 152 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 152 173
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 152 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 152 173 (accept_3_2 4 152 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  152 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 152 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 152 173 (Polychromatic418967fa.accept_12_2_8_5_1_408 2 152 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 152 173 (accept_3_2 1 152 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 152 173)))))))))))))))))))))) (allB_succ' 23 151 173 (Eq.refl Bool.true) (allA_of_3_0
  23 151 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 150 173 (Eq.refl Bool.true) (allA_succ_of_accept 23
  150 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 150 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 150 173 (accept_3_2 22 150 173 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 150 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 150 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 150 173 (Polychromatic418967fa.accept_16_4_6_13_1_1874 20 150
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 150 173 (accept_3_2 19 150
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 150 173
  (Polychromatic418967fa.accept_21_18_3_5_1_9796 18 150 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 150 173 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 150 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 150 173 (accept_3_2 16 150 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 150 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 150 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 150 173 (Polychromatic418967fa.accept_9_5_6_2_1_161
  14 150 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 150 173 (accept_3_2 13
  150 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 150 173
  (Polychromatic418967fa.accept_9_3_6_2_1_160 12 150 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 150 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 150 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 150 173 (accept_3_2 10 150 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 150 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 150 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 150 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 8
  150 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 150 173 (accept_3_2 7 150
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 150 173
  (Polychromatic418967fa.accept_13_6_7_4_1_2264 6 150 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 150 173 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 150 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 150 173 (accept_3_2 4 150 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 150 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 150 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 150 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 2
  150 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 150 173 (accept_3_2 1 150
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150 173)))))))))))))))))))))))) (allB_succ' 25 149 173 (Eq.refl
  Bool.true) (allA_succ_of_accept 24 149 173 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 149 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 149 173
  (Polychromatic418967fa.accept_13_10_6_4_1_1583 23 149 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 149 173 (accept_3_2 22 149 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 149 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 149 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 149 173 (Polychromatic418967fa.accept_13_7_6_4_1_933 20 149 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 149 173 (accept_3_2 19 149 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 149 173 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 149 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 149 173
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 149 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 149 173 (accept_3_2 16 149 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 149 173 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 149 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 149 173 (Polychromatic418967fa.accept_10_4_9_3_1_1907 14 149 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 149 173 (accept_3_2 13 149 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 149 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 149 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 149 173
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 149 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 149 173 (accept_3_2 10 149 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  149 173 (Polychromatic418967fa.accept_13_9_6_4_1_2243 9 149 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 149 173 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 149 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 149 173 (accept_3_2 7 149 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 149 173 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 149 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 149 173
  (Polychromatic418967fa.accept_13_5_6_4_1_1582 5 149 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 149 173 (accept_3_2 4 149 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  149 173 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 149 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 149 173 (Polychromatic418967fa.accept_13_2_6_4_1_1593 2 149 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 149 173 (accept_3_2 1 149 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 149 173))))))))))))))))))))))))) (allB_succ' 26 148 173 (Eq.refl Bool.true)
  (allA_of_3_0 26 148 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 27 147 173 (Eq.refl Bool.true)
  (allA_succ_of_accept 26 147 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 147 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 147 173 (accept_3_2 25 147 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 147 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 147 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 147 173 (Polychromatic418967fa.accept_9_5_3_2_1_171
  23 147 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 147 173 (accept_3_2 22
  147 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 147 173
  (Polychromatic418967fa.accept_12_9_3_5_1_423 21 147 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 147 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 147 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 173 (accept_3_2 19 147 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 147 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 147 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 147 173 (Polychromatic418967fa.accept_9_8_3_2_1_417
  17 147 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 147 173 (accept_3_2 16
  147 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 147 173
  (Polychromatic418967fa.accept_9_6_3_2_1_431 15 147 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 147 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 147 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 147 173 (accept_3_2 13 147 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 147 173 (Polychromatic418967fa.accept_11_1_4_8_1_1918 12 147 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 147 173
  (Polychromatic418967fa.accept_15_11_12_8_1_739 11 147 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 147 173 (accept_3_2 10 147 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  147 173 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 147 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 147 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 147 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 173 (accept_3_2 7 147 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 147 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 147 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 147 173
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 147 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 147 173 (accept_3_2 4 147 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  147 173 (Polychromatic418967fa.accept_15_3_12_8_1_738 3 147 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 147 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 147 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 173 (accept_3_2 1 147 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 147 173))))))))))))))))))))))))))) (allB_succ' 28 146 173 (Eq.refl Bool.true)
  (allA_succ_of_accept 27 146 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 146 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 146 173 (Polychromatic418967fa.accept_17_9_10_3_1_3423 26 146
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 146 173 (accept_3_2 25 146
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 146 173
  (Polychromatic418967fa.accept_17_7_10_3_1_1421 24 146 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 146 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 146 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 146 173 (accept_3_2 22 146 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 146 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 146 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 146 173 (Polychromatic418967fa.accept_12_8_2_5_1_844
  20 146 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 146 173 (accept_3_2 19
  146 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 146 173
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 146 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 146 173 (Polychromatic418967fa.accept_10_7_6_3_1_927 17 146 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 146 173 (accept_3_2 16 146 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 146 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 146 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 146 173 (Polychromatic418967fa.accept_13_1_3_4_1_925
  14 146 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 146 173 (accept_3_2 13
  146 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 146 173
  (Polychromatic418967fa.accept_13_12_3_4_1_928 12 146 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 146 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 146 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 146 173 (accept_3_2 10 146 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 146 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 146 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 146 173 (Polychromatic418967fa.accept_7_1_6_5_1_39 8
  146 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 146 173 (accept_3_2 7 146
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 146 173
  (Polychromatic418967fa.accept_11_6_3_8_1_843 6 146 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 146 173 (Polychromatic418967fa.accept_11_5_3_8_1_454 5 146 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 146 173 (accept_3_2 4 146 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 146 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 146 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 146 173 (Polychromatic418967fa.accept_21_2_20_5_1_6599
  2 146 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 146 173 (accept_3_2 1
  146 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146 173)))))))))))))))))))))))))))) (allB_succ' 29 145 173
  (Eq.refl Bool.true) (allA_of_3_0 29 145 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 30 144 173 (Eq.refl
  Bool.true) (allA_succ_of_accept 29 144 173 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 144 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 144 173 (accept_3_2 28 144 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 144 173 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 144 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 144 173
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 26 144 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 144 173 (accept_3_2 25 144 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 144 173 (Polychromatic418967fa.accept_21_3_18_5_1_8211 24 144 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 144 173 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 144 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 144 173 (accept_3_2 22 144 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 144 173 (Polychromatic418967fa.accept_25_21_19_23_1_9795 21 144 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 144 173
  (Polychromatic418967fa.accept_7_6_4_5_1_314 20 144 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 144 173 (accept_3_2 19 144 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 144 173 (Polychromatic418967fa.accept_13_5_1_4_1_3966 18 144 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 144 173 (Polychromatic418967fa.accept_10_7_4_3_1_560 17 144 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 144 173 (accept_3_2 16 144 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 144 173 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 144 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 144 173
  (Polychromatic418967fa.accept_15_14_9_8_1_3165 14 144 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 144 173 (accept_3_2 13 144 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 144 173 (Polychromatic418967fa.accept_17_12_8_3_1_4646 12 144 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 144 173 (Polychromatic418967fa.accept_20_11_4_13_1_9794 11 144 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 144 173 (accept_3_2 10 144 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 144 173 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 144 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 144 173
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 144 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 144 173 (accept_3_2 7 144 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  144 173 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 144 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 144 173 (Polychromatic418967fa.accept_13_5_1_4_1_3966 5 144 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 144 173 (accept_3_2 4 144 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 144 173 (Polychromatic418967fa.accept_13_3_1_4_1_945 3 144 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 144 173
  (Polychromatic418967fa.accept_7_2_4_5_1_313 2 144 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 144 173 (accept_3_2 1 144 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144
  173)))))))))))))))))))))))))))))) (allB_succ' 31 143 173 (Eq.refl Bool.true) (allA_succ_of_accept 30 143 173
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 143 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 143 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 143 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 143 173 (accept_3_2 28 143 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 143 173 (Polychromatic418967fa.accept_17_10_7_3_1_727 27 143 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 143 173
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 143 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 143 173 (accept_3_2 25 143 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 143 173 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 143 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 143 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 143 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 143 173 (accept_3_2 22 143 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 143 173 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 143 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 143 173
  (Polychromatic418967fa.accept_18_2_17_11_1_3178 20 143 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 143 173 (accept_3_2 19 143 173 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 143 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 143 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 143 173 (Polychromatic418967fa.accept_19_17_10_2_1_9793 17 143
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 143 173 (accept_3_2 16 143
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 143 173
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 143 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 143 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 143 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 143 173 (accept_3_2 13 143 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 143 173 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 143 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 143 173
  (Polychromatic418967fa.accept_19_11_10_2_1_9757 11 143 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 143 173 (accept_3_2 10 143 173 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 143 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 143 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 143 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 143 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 143 173 (accept_3_2 7 143 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 143 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 6
  143 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 143 173
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 143 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 143 173 (accept_3_2 4 143 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  143 173 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 143 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 143 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 143 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 143 173 (accept_3_2 1 143 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 143 173))))))))))))))))))))))))))))))) (allB_succ' 32 142 173 (Eq.refl Bool.true)
  (allA_of_3_0 32 142 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 141 173 (Eq.refl Bool.true)
  (allA_succ_of_accept 32 141 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 141 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 141 173 (accept_3_2 31 141 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 141 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 141 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 141 173
  (Polychromatic418967fa.accept_15_14_6_8_1_1410 29 141 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 141 173 (accept_3_2 28 141 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 141 173 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 141 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 141 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 141 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 173 (accept_3_2 25 141 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 141 173 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 141 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 141 173
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 141 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 141 173 (accept_3_2 22 141 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 141 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 141 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 141 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 141 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 141 173 (accept_3_2 19 141 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 141 173 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 141 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 141 173
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 141 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 141 173 (accept_3_2 16 141 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 141 173 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 141 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 141 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 141 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 173 (accept_3_2 13 141 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 141 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 141 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 141 173
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 141 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 141 173 (accept_3_2 10 141 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  141 173 (Polychromatic418967fa.accept_18_9_15_11_1_5693 9 141 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 141 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 141 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 173 (accept_3_2 7 141 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 141 173 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 141 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 141 173
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 141 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 141 173 (accept_3_2 4 141 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  141 173 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 141 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 141 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 141 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 173 (accept_3_2 1 141 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 141 173))))))))))))))))))))))))))))))))) (allB_succ' 34 140 173 (Eq.refl Bool.true)
  (allA_succ_of_accept 33 140 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 140 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 140 173 (Polychromatic418967fa.accept_13_6_10_4_1_957 32 140
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 140 173 (accept_3_2 31 140
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 140 173
  (Polychromatic418967fa.accept_9_3_5_2_1_28 30 140 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 140 173 (Polychromatic418967fa.accept_15_14_5_8_1_3175 29 140 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 140 173 (accept_3_2 28 140 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 140 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 140 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 140 173 (Polychromatic418967fa.accept_9_8_5_2_1_422
  26 140 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 140 173 (accept_3_2 25
  140 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 140 173
  (Polychromatic418967fa.accept_9_6_5_2_1_421 24 140 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 140 173 (Polychromatic418967fa.accept_18_5_14_11_1_2073 23 140 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 140 173 (accept_3_2 22 140 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 140 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 140 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 140 173
  (Polychromatic418967fa.accept_13_7_10_4_1_919 20 140 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 140 173 (accept_3_2 19 140 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 140 173 (Polychromatic418967fa.accept_13_5_10_4_1_1564 18 140 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 140 173 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 140 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 140 173 (accept_3_2 16 140 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 140 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 140 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 140 173
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 140 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 140 173 (accept_3_2 13 140 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 140 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 140 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 140 173 (Polychromatic418967fa.accept_13_11_10_4_1_1565 11 140 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 140 173 (accept_3_2 10 140 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 140 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 140 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 140 173
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 140 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 140 173 (accept_3_2 7 140 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  140 173 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 140 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 140 173 (Polychromatic418967fa.accept_13_5_10_4_1_1564 5 140 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 140 173 (accept_3_2 4 140 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 140 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 140 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 140 173
  (Polychromatic418967fa.accept_12_2_8_5_1_408 2 140 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 140 173 (accept_3_2 1 140 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140
  173)))))))))))))))))))))))))))))))))) (allB_succ' 35 139 173 (Eq.refl Bool.true) (allA_of_3_0 35 139 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 138 173 (Eq.refl Bool.true) (allA_succ_of_accept 35 138 173
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 138 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 138 173 (accept_3_2 34 138 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 138 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 138 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 138 173 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 138 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 138 173 (accept_3_2 31 138 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 138 173 (Polychromatic418967fa.accept_16_14_10_13_1_2768 30 138 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 138 173
  (Polychromatic418967fa.accept_19_10_5_2_1_9784 29 138 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 138 173 (accept_3_2 28 138 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 138 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 138 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 138 173 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 138 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 138 173 (accept_3_2 25 138 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 138 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 138 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 138 173
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 138 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 138 173 (accept_3_2 22 138 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 138 173 (Polychromatic418967fa.accept_10_1_8_3_1_947 21 138 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 138 173 (Polychromatic418967fa.accept_15_5_3_8_1_748 20 138 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 138 173 (accept_3_2 19 138 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 138 173 (Polychromatic418967fa.accept_17_1_2_3_1_4668 18 138
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 138 173
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 138 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 138 173 (accept_3_2 16 138 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 138 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 138 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 138 173 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 138 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 138 173 (accept_3_2 13 138 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 138 173 (Polychromatic418967fa.accept_13_12_8_4_1_3099 12 138 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 138 173
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 138 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 138 173 (accept_3_2 10 138 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  138 173 (Polychromatic418967fa.accept_13_9_8_4_1_937 9 138 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 138 173 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 138 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 138 173 (accept_3_2 7 138 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 138 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 138 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 138 173
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 138 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 138 173 (accept_3_2 4 138 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  138 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 138 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 138 173 (Polychromatic418967fa.accept_20_2_18_13_1_3843 2 138 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 138 173 (accept_3_2 1 138 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 138 173)))))))))))))))))))))))))))))))))))) (allB_succ' 37 137 173 (Eq.refl
  Bool.true) (allA_succ_of_accept 36 137 173 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 137 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 137 173 (Polychromatic418967fa.accept_10_5_7_3_1_561
  35 137 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 137 173 (accept_3_2 34
  137 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 137 173
  (Polychromatic418967fa.accept_16_1_9_13_1_1822 33 137 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 137 173 (Polychromatic418967fa.accept_13_6_7_4_1_2264 32 137 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 137 173 (accept_3_2 31 137 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 137 173 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 137 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 137 173 (Polychromatic418967fa.accept_7_1_4_5_1_35 29
  137 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 137 173 (accept_3_2 28
  137 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 137 173
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 137 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 137 173 (Polychromatic418967fa.accept_10_6_7_3_1_547 26 137 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 137 173 (accept_3_2 25 137 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 137 173 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 137 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 137 173 (Polychromatic418967fa.accept_7_2_4_5_1_313
  23 137 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 137 173 (accept_3_2 22
  137 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 137 173
  (Polychromatic418967fa.accept_15_6_2_8_1_2223 21 137 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 137 173 (Polychromatic418967fa.accept_7_6_4_5_1_314 20 137 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 137 173 (accept_3_2 19 137 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 137 173 (Polychromatic418967fa.accept_19_18_4_2_1_2841 18 137 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 137 173
  (Polychromatic418967fa.accept_16_1_9_13_1_1822 17 137 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 137 173 (accept_3_2 16 137 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 137 173 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 137 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 137 173 (Polychromatic418967fa.accept_10_4_7_3_1_54 14 137 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 137 173 (accept_3_2 13 137 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 137 173 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 137 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 137 173
  (Polychromatic418967fa.accept_13_11_7_4_1_1561 11 137 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 137 173 (accept_3_2 10 137 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  137 173 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 137 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 137 173 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 137 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 137 173 (accept_3_2 7 137 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 137 173 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 137 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 137 173
  (Polychromatic418967fa.accept_10_5_7_3_1_561 5 137 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 137 173 (accept_3_2 4 137 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  137 173 (Polychromatic418967fa.accept_11_3_5_8_1_458 3 137 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 137 173 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 137 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 137 173 (accept_3_2 1 137 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 137 173))))))))))))))))))))))))))))))))))))) (allB_succ' 38 136 173 (Eq.refl Bool.true)
  (allA_of_3_0 38 136 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 135 173 (Eq.refl Bool.true)
  (allA_succ_of_accept 38 135 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 135 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 135 173 (accept_3_2 37 135 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 135 173 (Polychromatic418967fa.accept_13_10_5_4_1_3107 36 135 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 135 173
  (Polychromatic418967fa.accept_13_9_5_4_1_1591 35 135 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 135 173 (accept_3_2 34 135 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 135 173 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 135 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 135 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 135 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 135 173 (accept_3_2 31 135 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 135 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 135 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 135 173
  (Polychromatic418967fa.accept_22_7_3_19_1_8158 29 135 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 135 173 (accept_3_2 28 135 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 135 173 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 135 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 135 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 135 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 135 173 (accept_3_2 25 135 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 135 173 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 135 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 135 173
  (Polychromatic418967fa.accept_13_10_5_4_1_3107 23 135 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 135 173 (accept_3_2 22 135 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 135 173 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 135 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 135 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 135 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 135 173 (accept_3_2 19 135 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 135 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 135 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 135 173
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 135 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 135 173 (accept_3_2 16 135 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 135 173 (Polychromatic418967fa.accept_13_2_5_4_1_3926 15 135 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 135 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 135 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 173 (accept_3_2 13 135 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 135 173 (Polychromatic418967fa.accept_10_2_5_3_1_1408 12 135 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 135 173
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 135 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 135 173 (accept_3_2 10 135 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  135 173 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 135 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 135 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 135 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 173 (accept_3_2 7 135 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 135 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 135 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 135 173
  (Polychromatic418967fa.accept_11_5_3_8_1_454 5 135 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 135 173 (accept_3_2 4 135 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  135 173 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 135 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 135 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 135 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 173 (accept_3_2 1 135 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 135 173))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 134 173 (Eq.refl
  Bool.true) (allA_succ_of_accept 39 134 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 134 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 134 173 (Polychromatic418967fa.accept_7_3_1_5_1_44 38
  134 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 134 173 (accept_3_2 37
  134 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 134 173
  (Polychromatic418967fa.accept_15_6_14_8_1_245 36 134 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 134 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 134 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 134 173 (accept_3_2 34 134 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 134 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 134 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 134 173 (Polychromatic418967fa.accept_7_4_1_5_1_540
  32 134 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 134 173 (accept_3_2 31
  134 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 134 173
  (Polychromatic418967fa.accept_9_3_8_2_1_162 30 134 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 134 173 (Polychromatic418967fa.accept_10_9_4_3_1_539 29 134 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 134 173 (accept_3_2 28 134 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 134 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 134 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 134 173 (Polychromatic418967fa.accept_19_7_1_2_1_9792
  26 134 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 134 173 (accept_3_2 25
  134 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 134 173
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 134 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 134 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 134 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 134 173 (accept_3_2 22 134 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 134 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 134 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 134 173 (Polychromatic418967fa.accept_7_6_1_5_1_322
  20 134 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 134 173 (accept_3_2 19
  134 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 134 173
  (Polychromatic418967fa.accept_7_4_1_5_1_540 18 134 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 134 173 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 134 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 134 173 (accept_3_2 16 134 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 134 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 134 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 134 173 (Polychromatic418967fa.accept_9_5_8_2_1_409
  14 134 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 134 173 (accept_3_2 13
  134 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 134 173
  (Polychromatic418967fa.accept_9_3_8_2_1_162 12 134 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 134 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 134 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 134 173 (accept_3_2 10 134 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 134 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 134 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 134 173 (Polychromatic418967fa.accept_12_8_2_5_1_844 8
  134 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 134 173 (accept_3_2 7 134
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 134 173
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 134 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 134 173 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 134 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 134 173 (accept_3_2 4 134 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 134 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 134 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 134 173 (Polychromatic418967fa.accept_21_2_8_5_1_5057
  2 134 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 134 173 (accept_3_2 1
  134 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134 173)))))))))))))))))))))))))))))))))))))))) (allB_succ'
  41 133 173 (Eq.refl Bool.true) (allA_of_3_0 41 133 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 132 173
  (Eq.refl Bool.true) (allA_succ_of_accept 41 132 173 (Polychromatic418967fa.accept_8_1_4_5_1_48 41 132 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 132 173 (accept_3_2 40 132 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 132 173 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 132 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 132 173
  (Polychromatic418967fa.accept_13_12_2_4_1_3131 38 132 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 132 173 (accept_3_2 37 132 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 132 173 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 132 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 132 173 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 132 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 132 173 (accept_3_2 34 132 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 132 173 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 132 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 132 173
  (Polychromatic418967fa.accept_7_4_6_5_1_141 32 132 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 132 173 (accept_3_2 31 132 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 132 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 132 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 132 173 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 132 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 132 173 (accept_3_2 28 132 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 132 173 (Polychromatic418967fa.accept_14_13_6_5_1_1853 27 132 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 132 173
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 132 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 132 173 (accept_3_2 25 132 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 132 173 (Polychromatic418967fa.accept_13_11_2_4_1_1590 24 132 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 132 173 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 132 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 132 173 (accept_3_2 22 132 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 132 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 132 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 132 173
  (Polychromatic418967fa.accept_15_5_12_8_1_3168 20 132 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 132 173 (accept_3_2 19 132 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 132 173 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 132 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 132 173 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 132 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 132 173 (accept_3_2 16 132 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 132 173 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 132 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 132 173
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 132 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 132 173 (accept_3_2 13 132 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 132 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 132 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 132 173 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 132 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 132 173 (accept_3_2 10 132 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 132 173 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 132 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 132 173
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 132 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 132 173 (accept_3_2 7 132 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  132 173 (Polychromatic418967fa.accept_13_6_2_4_1_923 6 132 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 132 173 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 132 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 132 173 (accept_3_2 4 132 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 132 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 132 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 132 173
  (Polychromatic418967fa.accept_25_2_7_23_1_9791 2 132 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 132 173 (accept_3_2 1 132 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132
  173)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 131 173 (Eq.refl Bool.true) (allA_succ_of_accept 42 131
  173 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 131 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 131 173 (Polychromatic418967fa.accept_17_7_12_3_1_4693 41 131 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 131 173 (accept_3_2 40 131 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 131 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 131 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 131 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 38
  131 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 131 173 (accept_3_2 37
  131 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 131 173
  (Polychromatic418967fa.accept_13_10_1_4_1_3103 36 131 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 131 173 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 131 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 131 173 (accept_3_2 34 131 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 131 173 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 131 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 131 173 (Polychromatic418967fa.accept_10_2_1_3_1_233
  32 131 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 131 173 (accept_3_2 31
  131 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 131 173
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 131 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 131 173 (Polychromatic418967fa.accept_13_3_1_4_1_945 29 131 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 131 173 (accept_3_2 28 131 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 131 173 (Polychromatic418967fa.accept_15_12_11_8_1_1392 27 131 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 131 173
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 131 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 131 173 (accept_3_2 25 131 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 131 173 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 131 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 131 173 (Polychromatic418967fa.accept_13_10_1_4_1_3103 23 131 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 131 173 (accept_3_2 22 131 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 131 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 131 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 131 173
  (Polychromatic418967fa.accept_11_9_10_8_1_444 20 131 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 131 173 (accept_3_2 19 131 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 131 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 131 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 131 173 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 131 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 131 173 (accept_3_2 16 131 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 131 173 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 131 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 131 173
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 131 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 131 173 (accept_3_2 13 131 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 131 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 131 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 131 173 (Polychromatic418967fa.accept_22_11_21_19_1_9790 11 131 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 131 173 (accept_3_2 10 131 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 131 173 (Polychromatic418967fa.accept_11_9_10_8_1_444 9 131 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 131 173
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 131 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 131 173 (accept_3_2 7 131 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  131 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 131 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 131 173 (Polychromatic418967fa.accept_13_5_1_4_1_3966 5 131 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 131 173 (accept_3_2 4 131 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 131 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 131 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 131 173
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 131 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 131 173 (accept_3_2 1 131 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 131
  173))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 130 173 (Eq.refl Bool.true) (allA_of_3_0 44 130 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 129 173 (Eq.refl Bool.true) (allA_succ_of_accept 44 129 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 129 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 129 173 (accept_3_2 43 129 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 129 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 129 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 129 173 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 129 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 129 173 (accept_3_2 40 129 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 129 173 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 129 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 129 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 129 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 129 173 (accept_3_2 37 129 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 129 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 129 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 129 173 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 129 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 129 173 (accept_3_2 34 129 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 129 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 129 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 129 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 129 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 129 173 (accept_3_2 31 129 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 129 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 129 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 129 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 129 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 129 173 (accept_3_2 28 129 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 129 173 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 129 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 129 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 129 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 129 173 (accept_3_2 25 129 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 129 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 129 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 129 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 129 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 173 (accept_3_2 22 129 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 129 173 (Polychromatic418967fa.accept_13_8_12_4_1_4858 21 129 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 129 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 129 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 129 173 (accept_3_2 19 129 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 129 173 (Polychromatic418967fa.accept_13_5_12_4_1_449 18 129 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 129 173 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 129 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 173 (accept_3_2 16 129 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 129 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 129 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 129 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 129 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 129 173 (accept_3_2 13 129 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 129 173 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 129 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 129 173 (Polychromatic418967fa.accept_13_11_12_4_1_3945 11 129 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 173 (accept_3_2 10 129 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 129 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 129 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 129 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 129 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 129 173 (accept_3_2 7 129 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  129 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 129 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 129 173 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 129 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 173 (accept_3_2 4 129 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 129 173 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 129 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 129 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 129 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 129 173 (accept_3_2 1 129 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129
  173))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 128 173 (Eq.refl Bool.true) (allA_succ_of_accept 45
  128 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 128 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 128 173 (Polychromatic418967fa.accept_17_10_9_3_1_7144 44 128 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 128 173 (accept_3_2 43 128 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 128 173 (Polychromatic418967fa.accept_19_4_14_2_1_4117 42 128
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 128 173
  (Polychromatic418967fa.accept_10_1_8_3_1_947 41 128 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 128 173 (accept_3_2 40 128 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 128 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 128 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 128 173 (Polychromatic418967fa.accept_7_3_2_5_1_147 38 128 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 128 173 (accept_3_2 37 128 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 128 173 (Polychromatic418967fa.accept_10_6_8_3_1_930 36 128 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 128 173
  (Polychromatic418967fa.accept_10_5_8_3_1_229 35 128 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 128 173 (accept_3_2 34 128 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 128 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 128 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 128 173 (Polychromatic418967fa.accept_7_4_2_5_1_527 32 128 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 128 173 (accept_3_2 31 128 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 128 173 (Polychromatic418967fa.accept_22_8_18_19_1_9789 30 128 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 128 173
  (Polychromatic418967fa.accept_21_8_2_5_1_8163 29 128 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 128 173 (accept_3_2 28 128 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 128 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 128 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 128 173 (Polychromatic418967fa.accept_10_6_8_3_1_930 26 128 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 128 173 (accept_3_2 25 128 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 128 173 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 128 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 128 173
  (Polychromatic418967fa.accept_13_10_11_4_1_2248 23 128 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 128 173 (accept_3_2 22 128 173 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 128 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 128 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 128 173 (Polychromatic418967fa.accept_13_7_11_4_1_2247 20 128
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 128 173 (accept_3_2 19 128
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 128 173
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 128 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 128 173 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 128 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 128 173 (accept_3_2 16 128 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 128 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 128 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 128 173 (Polychromatic418967fa.accept_12_2_8_5_1_408
  14 128 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 128 173 (accept_3_2 13
  128 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 128 173
  (Polychromatic418967fa.accept_13_12_11_4_1_3111 12 128 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 128 173 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 128 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 128 173 (accept_3_2 10 128 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 128 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 128 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 128 173
  (Polychromatic418967fa.accept_13_8_11_4_1_1553 8 128 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 128 173 (accept_3_2 7 128 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  128 173 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 128 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 128 173 (Polychromatic418967fa.accept_10_5_8_3_1_229 5 128 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 128 173 (accept_3_2 4 128 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 128 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 128 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 128 173
  (Polychromatic418967fa.accept_12_2_8_5_1_408 2 128 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 128 173 (accept_3_2 1 128 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128
  173)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 127 173 (Eq.refl Bool.true) (allA_of_3_0 47 127 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 126 173 (Eq.refl Bool.true) (allA_succ_of_accept 47 126 173
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 126 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 126 173 (accept_3_2 46 126 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 126 173 (Polychromatic418967fa.accept_13_6_9_4_1_2288 45 126 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 126 173 (Polychromatic418967fa.accept_13_5_9_4_1_441 44 126 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 126 173 (accept_3_2 43 126 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 126 173 (Polychromatic418967fa.accept_16_10_14_13_1_1870 42
  126 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 126 173
  (Polychromatic418967fa.accept_19_3_12_2_1_9788 41 126 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 126 173 (accept_3_2 40 126 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 126 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 126 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 126 173 (Polychromatic418967fa.accept_10_8_6_3_1_1394 38 126 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 126 173 (accept_3_2 37 126 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 126 173 (Polychromatic418967fa.accept_11_3_5_8_1_458 36 126
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 126 173
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 126 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 126 173 (accept_3_2 34 126 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 126 173 (Polychromatic418967fa.accept_13_7_9_4_1_918 33 126 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 126 173 (Polychromatic418967fa.accept_13_6_9_4_1_2288 32 126 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 126 173 (accept_3_2 31 126 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 126 173 (Polychromatic418967fa.accept_22_8_16_19_1_9787 30 126
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 126 173
  (Polychromatic418967fa.accept_10_9_6_3_1_545 29 126 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 126 173 (accept_3_2 28 126 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 126 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 126 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 126 173 (Polychromatic418967fa.accept_16_10_14_13_1_1870 26 126 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 126 173 (accept_3_2 25 126 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 126 173 (Polychromatic418967fa.accept_11_2_5_8_1_470 24 126
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 126 173
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 126 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 126 173 (accept_3_2 22 126 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 126 173 (Polychromatic418967fa.accept_13_8_9_4_1_1552 21 126 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 126 173 (Polychromatic418967fa.accept_13_7_9_4_1_918 20 126 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 126 173 (accept_3_2 19 126 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 126 173 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 126
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 126 173
  (Polychromatic418967fa.accept_10_7_6_3_1_927 17 126 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 126 173 (accept_3_2 16 126 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 126 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 126 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 126 173 (Polychromatic418967fa.accept_11_3_5_8_1_458 14 126 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 126 173 (accept_3_2 13 126 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 126 173 (Polychromatic418967fa.accept_17_12_7_3_1_1498 12 126
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 126 173
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 126 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 126 173 (accept_3_2 10 126 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  126 173 (Polychromatic418967fa.accept_10_9_6_3_1_545 9 126 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 126 173 (Polychromatic418967fa.accept_10_8_6_3_1_1394 8 126 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 126 173 (accept_3_2 7 126 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 126 173 (Polychromatic418967fa.accept_13_6_9_4_1_2288 6 126 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 126 173
  (Polychromatic418967fa.accept_13_5_9_4_1_441 5 126 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 126 173 (accept_3_2 4 126 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  126 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 126 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 126 173 (Polychromatic418967fa.accept_11_2_5_8_1_470 2 126 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 126 173 (accept_3_2 1 126 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 126 173)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 125 173 (Eq.refl
  Bool.true) (allA_succ_of_accept 48 125 173 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 125 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 125 173 (Polychromatic418967fa.accept_10_7_5_3_1_542
  47 125 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 125 173 (accept_3_2 46
  125 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 125 173
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 45 125 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 125 173 (Polychromatic418967fa.accept_15_14_5_8_1_3175 44 125 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 125 173 (accept_3_2 43 125 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 125 173 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 125 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 125 173 (Polychromatic418967fa.accept_9_5_8_2_1_409
  41 125 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 125 173 (accept_3_2 40
  125 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 125 173
  (Polychromatic418967fa.accept_7_4_6_5_1_141 39 125 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 125 173 (Polychromatic418967fa.accept_10_8_5_3_1_543 38 125 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 125 173 (accept_3_2 37 125 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 125 173 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 125 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 125 173 (Polychromatic418967fa.accept_13_9_8_4_1_937
  35 125 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 125 173 (accept_3_2 34
  125 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 125 173
  (Polychromatic418967fa.accept_9_6_8_2_1_410 33 125 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 125 173 (Polychromatic418967fa.accept_7_4_6_5_1_141 32 125 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 125 173 (accept_3_2 31 125 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 125 173 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 125 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 125 173 (Polychromatic418967fa.accept_7_1_6_5_1_39 29
  125 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 125 173 (accept_3_2 28
  125 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 125 173
  (Polychromatic418967fa.accept_10_7_5_3_1_542 27 125 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 125 173 (Polychromatic418967fa.accept_15_11_5_8_1_3157 26 125 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 125 173 (accept_3_2 25 125 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 125 173 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 125 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 125 173 (Polychromatic418967fa.accept_9_5_8_2_1_409
  23 125 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 125 173 (accept_3_2 22
  125 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 125 173
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 125 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 125 173 (Polychromatic418967fa.accept_14_6_13_5_1_534 20 125 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 125 173 (accept_3_2 19 125 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 125 173 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 125 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 125 173 (Polychromatic418967fa.accept_10_7_5_3_1_542
  17 125 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 125 173 (accept_3_2 16
  125 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 125 173
  (Polychromatic418967fa.accept_7_1_6_5_1_39 15 125 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 125 173 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 125 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 125 173 (accept_3_2 13 125 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 125 173 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 125 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 125 173 (Polychromatic418967fa.accept_7_4_6_5_1_141
  11 125 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 125 173 (accept_3_2 10
  125 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 125 173
  (Polychromatic418967fa.accept_13_9_8_4_1_937 9 125 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 125 173 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 125 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 125 173 (accept_3_2 7 125 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 125 173 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 125 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 125 173 (Polychromatic418967fa.accept_9_5_8_2_1_409 5
  125 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 125 173 (accept_3_2 4 125
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 125 173
  (Polychromatic418967fa.accept_9_3_8_2_1_162 3 125 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 125 173 (Polychromatic418967fa.accept_10_2_5_3_1_1408 2 125 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 125 173 (accept_3_2 1 125 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 125 173))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 124 173 (Eq.refl
  Bool.true) (allA_of_3_0 50 124 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 123 173 (Eq.refl Bool.true)
  (allA_succ_of_accept 50 123 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 123 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 123 173 (accept_3_2 49 123 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 123 173 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 123 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 123 173
  (Polychromatic418967fa.accept_17_13_4_3_1_1446 47 123 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 123 173 (accept_3_2 46 123 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 123 173 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 123 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 123 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 123 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 123 173 (accept_3_2 43 123 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 123 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 123 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 123 173
  (Polychromatic418967fa.accept_7_6_4_5_1_314 41 123 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 123 173 (accept_3_2 40 123 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 123 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 123 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 123 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 123 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 123 173 (accept_3_2 37 123 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 123 173 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 123 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 123 173
  (Polychromatic418967fa.accept_9_8_6_2_1_744 35 123 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 123 173 (accept_3_2 34 123 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 123 173 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 123 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 123 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 123 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 173 (accept_3_2 31 123 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 123 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 123 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 123 173
  (Polychromatic418967fa.accept_7_1_4_5_1_35 29 123 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 123 173 (accept_3_2 28 123 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 123 173 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 123 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 123 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 123 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 173 (accept_3_2 25 123 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 123 173 (Polychromatic418967fa.accept_13_11_6_4_1_3121 24 123 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 123 173
  (Polychromatic418967fa.accept_7_2_4_5_1_313 23 123 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 123 173 (accept_3_2 22 123 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 123 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 123 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 123 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 123 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 173 (accept_3_2 19 123 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 123 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 123 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 123 173
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 123 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 123 173 (accept_3_2 16 123 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 123 173 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 123 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 123 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 123 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 173 (accept_3_2 13 123 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 123 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 123 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 123 173
  (Polychromatic418967fa.accept_13_11_6_4_1_3121 11 123 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 123 173 (accept_3_2 10 123 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  123 173 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 123 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 123 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 123 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 173 (accept_3_2 7 123 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 123 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 123 173
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 123 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 123 173 (accept_3_2 4 123 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  123 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 123 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 123 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 123 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 173 (accept_3_2 1 123 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 123 173))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 122 173
  (Eq.refl Bool.true) (allA_succ_of_accept 51 122 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 122 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 122 173
  (Polychromatic418967fa.accept_7_1_3_5_1_33 50 122 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 122 173 (accept_3_2 49 122 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 122 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 122 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 122 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 122 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 122 173 (accept_3_2 46 122 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 122 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 122 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 122 173
  (Polychromatic418967fa.accept_7_2_3_5_1_34 44 122 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 122 173 (accept_3_2 43 122 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 122 173 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 122 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 122 173 (Polychromatic418967fa.accept_10_1_2_3_1_1910 41 122 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 122 173 (accept_3_2 40 122 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 122 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 122 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 122 173
  (Polychromatic418967fa.accept_13_12_5_4_1_3133 38 122 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 122 173 (accept_3_2 37 122 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 122 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 122 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 122 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 122 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 122 173 (accept_3_2 34 122 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 122 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 122 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 122 173
  (Polychromatic418967fa.accept_12_8_2_5_1_844 32 122 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 122 173 (accept_3_2 31 122 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 122 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 122 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 122 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 122 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 122 173 (accept_3_2 28 122 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 122 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 122 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 122 173
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 122 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 122 173 (accept_3_2 25 122 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 122 173 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 122 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 122 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 122 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 122 173 (accept_3_2 22 122 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 122 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 122 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 122 173
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 122 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 122 173 (accept_3_2 19 122 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 122 173 (Polychromatic418967fa.accept_20_18_2_13_1_5265 18 122 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 122 173 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 122 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 122 173 (accept_3_2 16 122 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 122 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 122 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 122 173
  (Polychromatic418967fa.accept_13_1_5_4_1_463 14 122 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 122 173 (accept_3_2 13 122 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 122 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 122 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 122 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 122 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 122 173 (accept_3_2 10 122 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 122 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 122 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 122 173
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 122 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 122 173 (accept_3_2 7 122 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  122 173 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 122 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 122 173 (Polychromatic418967fa.accept_10_5_2_3_1_239 5 122 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 122 173 (accept_3_2 4 122 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 122 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 122 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 122 173
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 122 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 122 173 (accept_3_2 1 122 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  173)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 121 173 (Eq.refl Bool.true) (allA_of_3_0 53 121
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 54 120 173 (Eq.refl Bool.true) (allA_succ_of_accept 53 120
  173 (Polychromatic418967fa.accept_7_4_1_5_1_540 53 120 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 120 173 (accept_3_2 52 120 173 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 120 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 120 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 120 173 (Polychromatic418967fa.accept_9_5_3_2_1_171 50 120 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 120 173 (accept_3_2 49 120 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 120 173 (Polychromatic418967fa.accept_7_6_1_5_1_322
  48 120 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 120 173
  (Polychromatic418967fa.accept_25_22_20_23_1_9786 47 120 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 120 173 (accept_3_2 46 120 173 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 120 173 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 120 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 120 173 (Polychromatic418967fa.accept_9_8_3_2_1_417 44 120 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 120 173 (accept_3_2 43 120 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 120 173 (Polychromatic418967fa.accept_9_6_3_2_1_431
  42 120 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 120 173
  (Polychromatic418967fa.accept_7_6_1_5_1_322 41 120 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 120 173 (accept_3_2 40 120 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 120 173 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 120 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 120 173 (Polychromatic418967fa.accept_7_3_1_5_1_44 38 120 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 120 173 (accept_3_2 37 120 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 120 173 (Polychromatic418967fa.accept_16_4_8_13_1_1059 36 120 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 120 173
  (Polychromatic418967fa.accept_9_8_3_2_1_417 35 120 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 120 173 (accept_3_2 34 120 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 120 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 120 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 120 173 (Polychromatic418967fa.accept_7_4_1_5_1_540 32 120 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 120 173 (accept_3_2 31 120 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 120 173 (Polychromatic418967fa.accept_21_9_15_5_1_3500 30 120 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 120 173
  (Polychromatic418967fa.accept_19_10_6_2_1_6907 29 120 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 120 173 (accept_3_2 28 120 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 120 173 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 120 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 120 173 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 120 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 120 173 (accept_3_2 25 120 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 120 173 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 120 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 120 173
  (Polychromatic418967fa.accept_9_5_3_2_1_171 23 120 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 120 173 (accept_3_2 22 120 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 120 173 (Polychromatic418967fa.accept_16_5_8_13_1_2764 21 120 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 120 173 (Polychromatic418967fa.accept_7_6_1_5_1_322 20 120 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 120 173 (accept_3_2 19 120 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 120 173 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 120 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 120 173
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 120 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 120 173 (accept_3_2 16 120 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 120 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 120 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 120 173 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 120 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 120 173 (accept_3_2 13 120 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 120 173 (Polychromatic418967fa.accept_13_12_3_4_1_928 12 120 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 120 173
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 120 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 120 173 (accept_3_2 10 120 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  120 173 (Polychromatic418967fa.accept_11_9_10_8_1_444 9 120 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 120 173 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 120 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 120 173 (accept_3_2 7 120 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 120 173 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 120 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 120 173
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 120 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 120 173 (accept_3_2 4 120 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  120 173 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 120 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 120 173 (Polychromatic418967fa.accept_17_2_1_3_1_2357 2 120 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 120 173 (accept_3_2 1 120 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 120 173)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 119 173
  (Eq.refl Bool.true) (allA_succ_of_accept 54 119 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 119 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 119 173
  (Polychromatic418967fa.accept_21_11_14_5_1_6596 53 119 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 119 173 (accept_3_2 52 119 173 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 119 173 (Polychromatic418967fa.accept_13_12_2_4_1_3131 51 119 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 119 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 119 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 119 173 (accept_3_2 49 119 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 119 173
  (Polychromatic418967fa.accept_19_10_5_2_1_9784 48 119 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 119 173 (Polychromatic418967fa.accept_23_1_4_12_1_9785 47 119 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 119 173 (accept_3_2 46 119 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 119 173 (Polychromatic418967fa.accept_13_6_2_4_1_923 45 119 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 119 173
  (Polychromatic418967fa.accept_10_4_9_3_1_1907 44 119 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 119 173 (accept_3_2 43 119 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 119 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 119 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 119 173 (Polychromatic418967fa.accept_16_9_7_13_1_4997 41 119 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 119 173 (accept_3_2 40 119 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 119 173 (Polychromatic418967fa.accept_15_9_14_8_1_1396 39 119
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 119 173
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 119 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 119 173 (accept_3_2 37 119 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 119 173 (Polychromatic418967fa.accept_10_6_9_3_1_935 36 119 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 119 173 (Polychromatic418967fa.accept_15_5_14_8_1_1376 35 119 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 119 173 (accept_3_2 34 119 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 119 173 (Polychromatic418967fa.accept_19_14_5_2_1_6941 33 119
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 119 173
  (Polychromatic418967fa.accept_11_10_9_8_1_1974 32 119 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 119 173 (accept_3_2 31 119 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 119 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 119 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 119 173 (Polychromatic418967fa.accept_19_10_5_2_1_9784 29 119 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 119 173 (accept_3_2 28 119 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 119 173 (Polychromatic418967fa.accept_19_8_5_2_1_4105 27 119
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 119 173
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 119 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 119 173 (accept_3_2 25 119 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 119 173 (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 119 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 119 173 (Polychromatic418967fa.accept_14_9_7_5_1_1105 23 119 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 119 173 (accept_3_2 22 119 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 119 173 (Polychromatic418967fa.accept_11_10_9_8_1_1974 21 119
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 119 173
  (Polychromatic418967fa.accept_15_5_14_8_1_1376 20 119 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 119 173 (accept_3_2 19 119 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 119 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 119 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 119 173 (Polychromatic418967fa.accept_19_17_5_2_1_2843 17 119 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 119 173 (accept_3_2 16 119 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 119 173 (Polychromatic418967fa.accept_21_15_14_5_1_9783 15 119
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 119 173
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 119 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 119 173 (accept_3_2 13 119 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 119 173 (Polychromatic418967fa.accept_13_12_2_4_1_3131 12 119 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 119 173 (Polychromatic418967fa.accept_13_11_2_4_1_1590 11 119 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 173 (accept_3_2 10 119 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 119 173 (Polychromatic418967fa.accept_14_9_7_5_1_1105 9 119 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 173
  (Polychromatic418967fa.accept_19_8_5_2_1_4105 8 119 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 119 173 (accept_3_2 7 119 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  119 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 119 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 119 173 (Polychromatic418967fa.accept_13_5_2_4_1_3955 5 119 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 173 (accept_3_2 4 119 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 119 173 (Polychromatic418967fa.accept_19_3_5_2_1_4103 3 119 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 173
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 119 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 119 173 (accept_3_2 1 119 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  173))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 118 173 (Eq.refl Bool.true) (allA_of_3_0 56
  118 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 57 117 173 (Eq.refl Bool.true) (allA_succ_of_accept 56
  117 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 117 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 117 173 (accept_3_2 55 117 173 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 117 173 (Polychromatic418967fa.accept_10_4_7_3_1_54 54 117 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 117 173 (Polychromatic418967fa.accept_21_11_12_5_1_2224 53 117
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 117 173 (accept_3_2 52 117
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 117 173
  (Polychromatic418967fa.accept_12_3_9_5_1_853 51 117 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 117 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 117 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 117 173 (accept_3_2 49 117 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 117 173 (Polychromatic418967fa.accept_11_4_7_8_1_1926 48 117 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 117 173
  (Polychromatic418967fa.accept_22_3_7_19_1_9782 47 117 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 117 173 (accept_3_2 46 117 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 117 173 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 117 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 117 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 117 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 173 (accept_3_2 43 117 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 117 173 (Polychromatic418967fa.accept_16_10_5_13_1_8591 42 117 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 117 173
  (Polychromatic418967fa.accept_15_11_12_8_1_739 41 117 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 117 173 (accept_3_2 40 117 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 117 173 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 117 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 117 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 117 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 173 (accept_3_2 37 117 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 117 173 (Polychromatic418967fa.accept_10_6_7_3_1_547 36 117 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 117 173
  (Polychromatic418967fa.accept_10_5_7_3_1_561 35 117 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 117 173 (accept_3_2 34 117 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 117 173 (Polychromatic418967fa.accept_15_3_12_8_1_738 33 117 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 117 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 117 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 173 (accept_3_2 31 117 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 117 173 (Polychromatic418967fa.accept_18_12_9_11_1_4370 30 117 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 117 173
  (Polychromatic418967fa.accept_17_12_15_3_1_7168 29 117 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 117 173 (accept_3_2 28 117 173 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 117 173 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 117 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 117 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 117 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 173 (accept_3_2 25 117 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 117 173 (Polychromatic418967fa.accept_10_4_7_3_1_54
  24 117 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 117 173
  (Polychromatic418967fa.accept_24_23_21_5_1_9781 23 117 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 117 173 (accept_3_2 22 117 173 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 117 173 (Polychromatic418967fa.accept_22_21_7_19_1_9780 21 117 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 117 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 20
  117 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 173 (accept_3_2 19
  117 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 117 173
  (Polychromatic418967fa.accept_15_3_12_8_1_738 18 117 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 117 173 (Polychromatic418967fa.accept_16_1_5_13_1_1025 17 117 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 173 (accept_3_2 16 117 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 117 173 (Polychromatic418967fa.accept_10_5_7_3_1_561 15 117 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 117 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 117 173 (accept_3_2 13 117 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 117 173 (Polychromatic418967fa.accept_17_12_15_3_1_7168 12 117 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 117 173 (Polychromatic418967fa.accept_15_11_12_8_1_739 11 117 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 173 (accept_3_2 10 117 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 173 (Polychromatic418967fa.accept_16_9_5_13_1_4972 9 117
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 117 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 117 173 (accept_3_2 7 117 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  117 173 (Polychromatic418967fa.accept_10_6_7_3_1_547 6 117 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 117 173 (Polychromatic418967fa.accept_10_5_7_3_1_561 5 117 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 173 (accept_3_2 4 117 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 117 173 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 117 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 117 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 117 173 (accept_3_2 1 117 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  173))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 116 173 (Eq.refl Bool.true)
  (allA_succ_of_accept 57 116 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 116 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 116 173 (Polychromatic418967fa.accept_16_8_4_13_1_1014 56 116
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 116 173 (accept_3_2 55 116
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 116 173
  (Polychromatic418967fa.accept_13_2_12_4_1_943 54 116 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 116 173 (Polychromatic418967fa.accept_17_2_14_3_1_4679 53 116 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 116 173 (accept_3_2 52 116 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 116 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 116 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 116 173 (Polychromatic418967fa.accept_7_1_4_5_1_35 50
  116 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 116 173 (accept_3_2 49
  116 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 116 173
  (Polychromatic418967fa.accept_7_6_4_5_1_314 48 116 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 116 173 (Polychromatic418967fa.accept_10_7_6_3_1_927 47 116 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 116 173 (accept_3_2 46 116 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 116 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 116 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 116 173 (Polychromatic418967fa.accept_7_2_4_5_1_313
  44 116 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 116 173 (accept_3_2 43
  116 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 116 173
  (Polychromatic418967fa.accept_9_6_8_2_1_410 42 116 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 116 173 (Polychromatic418967fa.accept_7_6_4_5_1_314 41 116 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 116 173 (accept_3_2 40 116 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 116 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 116 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 116 173 (Polychromatic418967fa.accept_10_8_6_3_1_1394
  38 116 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 116 173 (accept_3_2 37
  116 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 116 173
  (Polychromatic418967fa.accept_7_1_4_5_1_35 36 116 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 116 173 (Polychromatic418967fa.accept_15_5_11_8_1_1391 35 116 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 116 173 (accept_3_2 34 116 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 116 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 116 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 116 173 (Polychromatic418967fa.accept_9_5_8_2_1_409
  32 116 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 116 173 (accept_3_2 31
  116 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 116 173
  (Polychromatic418967fa.accept_7_2_4_5_1_313 30 116 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 116 173 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 116 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 116 173 (accept_3_2 28 116 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 116 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 116 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 116 173 (Polychromatic418967fa.accept_12_2_8_5_1_408
  26 116 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 116 173 (accept_3_2 25
  116 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 116 173
  (Polychromatic418967fa.accept_9_6_8_2_1_410 24 116 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 116 173 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 116 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 116 173 (accept_3_2 22 116 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 116 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 116 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 116 173 (Polychromatic418967fa.accept_7_6_4_5_1_314
  20 116 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 116 173 (accept_3_2 19
  116 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 116 173
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 116 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 116 173 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 116 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 116 173 (accept_3_2 16 116 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 116 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 116 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 116 173 (Polychromatic418967fa.accept_9_5_8_2_1_409
  14 116 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 116 173 (accept_3_2 13
  116 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 116 173
  (Polychromatic418967fa.accept_9_3_8_2_1_162 12 116 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 116 173 (Polychromatic418967fa.accept_13_11_12_4_1_3945 11 116 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 116 173 (accept_3_2 10 116 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 116 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 116 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 116 173
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 116 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 116 173 (accept_3_2 7 116 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  116 173 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 116 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 116 173 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 116 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 116 173 (accept_3_2 4 116 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 116 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 116 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 116 173
  (Polychromatic418967fa.accept_7_2_4_5_1_313 2 116 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 116 173 (accept_3_2 1 116 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  173)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 115 173 (Eq.refl Bool.true) (allA_of_3_0
  59 115 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 114 173 (Eq.refl Bool.true) (allA_succ_of_accept 59
  114 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 114 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 114 173 (accept_3_2 58 114 173 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 114 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 114 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 114 173 (Polychromatic418967fa.accept_11_1_4_8_1_1918 56 114
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 114 173 (accept_3_2 55 114
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 114 173
  (Polychromatic418967fa.accept_21_12_9_5_1_6547 54 114 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 114 173 (Polychromatic418967fa.accept_7_4_2_5_1_527 53 114 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 114 173 (accept_3_2 52 114 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 114 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 114 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 114 173 (Polychromatic418967fa.accept_9_5_6_2_1_161
  50 114 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 114 173 (accept_3_2 49
  114 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 114 173
  (Polychromatic418967fa.accept_9_3_6_2_1_160 48 114 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 114 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 114 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 114 173 (accept_3_2 46 114 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 114 173 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 114 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 114 173 (Polychromatic418967fa.accept_9_8_6_2_1_744
  44 114 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 114 173 (accept_3_2 43
  114 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 114 173
  (Polychromatic418967fa.accept_17_8_12_3_1_5927 42 114 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 114 173 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 114 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 114 173 (accept_3_2 40 114 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 114 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 114 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 114 173 (Polychromatic418967fa.accept_7_3_2_5_1_147
  38 114 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 114 173 (accept_3_2 37
  114 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 114 173
  (Polychromatic418967fa.accept_21_15_9_5_1_6588 36 114 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 114 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 114 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 114 173 (accept_3_2 34 114 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 114 173 (Polychromatic418967fa.accept_13_7_10_4_1_919 33 114 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 114 173
  (Polychromatic418967fa.accept_7_4_2_5_1_527 32 114 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 114 173 (accept_3_2 31 114 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 114 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 114 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 114 173 (Polychromatic418967fa.accept_10_9_4_3_1_539 29 114 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 114 173 (accept_3_2 28 114 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 114 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 114 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 114 173
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 114 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 114 173 (accept_3_2 25 114 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 114 173 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 114 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 114 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 114 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 114 173 (accept_3_2 22 114 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 114 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 114 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 114 173
  (Polychromatic418967fa.accept_13_7_10_4_1_919 20 114 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 114 173 (accept_3_2 19 114 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 114 173 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 114 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 114 173 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 114 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 114 173 (accept_3_2 16 114 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 114 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 114 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 114 173
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 114 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 114 173 (accept_3_2 13 114 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 114 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 114 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 114 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 114 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 114 173 (accept_3_2 10 114 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 114 173 (Polychromatic418967fa.accept_10_9_4_3_1_539 9 114 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 114 173
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 114 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 114 173 (accept_3_2 7 114 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  114 173 (Polychromatic418967fa.accept_13_6_10_4_1_957 6 114 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 114 173 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 114 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 114 173 (accept_3_2 4 114 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 114 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 114 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 114 173
  (Polychromatic418967fa.accept_15_2_9_8_1_736 2 114 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 114 173 (accept_3_2 1 114 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  173)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 113 173 (Eq.refl Bool.true)
  (allA_succ_of_accept 60 113 173 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 113 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 113 173 (Polychromatic418967fa.accept_7_3_1_5_1_44 59 113 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 113 173 (accept_3_2 58 113 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 113 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 57
  113 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 113 173
  (Polychromatic418967fa.accept_21_14_8_5_1_6586 56 113 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 113 173 (accept_3_2 55 113 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 113 173 (Polychromatic418967fa.accept_19_16_18_2_1_6934 54 113 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 113 173 (Polychromatic418967fa.accept_7_4_1_5_1_540 53 113 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 113 173 (accept_3_2 52 113 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 113 173 (Polychromatic418967fa.accept_9_6_5_2_1_421 51 113 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 113 173
  (Polychromatic418967fa.accept_11_6_3_8_1_843 50 113 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 113 173 (accept_3_2 49 113 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 113 173 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 113 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 113 173 (Polychromatic418967fa.accept_13_8_9_4_1_1552 47 113 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 113 173 (accept_3_2 46 113 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 113 173 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 113 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 113 173
  (Polychromatic418967fa.accept_8_4_1_5_1_186 44 113 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 113 173 (accept_3_2 43 113 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 113 173 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 113 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 113 173 (Polychromatic418967fa.accept_7_6_1_5_1_322 41 113 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 113 173 (accept_3_2 40 113 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 113 173 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 113 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 113 173
  (Polychromatic418967fa.accept_7_3_1_5_1_44 38 113 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 113 173 (accept_3_2 37 113 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 113 173 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 113 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 113 173 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 113 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 113 173 (accept_3_2 34 113 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 113 173 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 113 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 113 173
  (Polychromatic418967fa.accept_7_4_1_5_1_540 32 113 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 113 173 (accept_3_2 31 113 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 113 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 113 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 113 173 (Polychromatic418967fa.accept_19_10_18_2_1_6936 29 113 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 113 173 (accept_3_2 28 113 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 113 173 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 113 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 113 173
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 113 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 113 173 (accept_3_2 25 113 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 113 173 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 113 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 113 173 (Polychromatic418967fa.accept_19_4_18_2_1_9779 23 113 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 113 173 (accept_3_2 22 113 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 113 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 113 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 173
  (Polychromatic418967fa.accept_7_6_1_5_1_322 20 113 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 113 173 (accept_3_2 19 113 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 113 173 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 113 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 113 173 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 113 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 173 (accept_3_2 16 113 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 113 173 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 113 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 173
  (Polychromatic418967fa.accept_16_14_1_13_1_2754 14 113 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 113 173 (accept_3_2 13 113 173 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 113 173 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 113 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 113 173 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 113 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 173 (accept_3_2 10 113 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 173 (Polychromatic418967fa.accept_16_9_1_13_1_1850
  9 113 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 173
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 113 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 113 173 (accept_3_2 7 113 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  113 173 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 113 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 113 173 (Polychromatic418967fa.accept_11_5_3_8_1_454 5 113 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 173 (accept_3_2 4 113 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 173 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 113 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 173
  (Polychromatic418967fa.accept_17_2_11_3_1_4654 2 113 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 173 (accept_3_2 1 113 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  173))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 112 173 (Eq.refl Bool.true)
  (allA_of_3_0 62 112 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 63 111 173 (Eq.refl Bool.true)
  (allA_succ_of_accept 62 111 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 111 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 111 173 (accept_3_2 61 111 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 111 173 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 111 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 111 173 (Polychromatic418967fa.accept_9_5_3_2_1_171
  59 111 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 111 173 (accept_3_2 58
  111 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 111 173
  (Polychromatic418967fa.accept_7_1_6_5_1_39 57 111 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 111 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 111 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 173 (accept_3_2 55 111 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 111 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 111 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 111 173 (Polychromatic418967fa.accept_7_4_6_5_1_141
  53 111 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 111 173 (accept_3_2 52
  111 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 111 173
  (Polychromatic418967fa.accept_9_6_3_2_1_431 51 111 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 111 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 111 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 173 (accept_3_2 49 111 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 111 173 (Polychromatic418967fa.accept_10_8_1_3_1_1374 48 111 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 111 173
  (Polychromatic418967fa.accept_15_2_6_8_1_754 47 111 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 111 173 (accept_3_2 46 111 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 111 173 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 111 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 111 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 111 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 173 (accept_3_2 43 111 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 111 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 111 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 111 173
  (Polychromatic418967fa.accept_9_5_3_2_1_171 41 111 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 111 173 (accept_3_2 40 111 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 111 173 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 111 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 111 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 111 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 173 (accept_3_2 37 111 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 111 173 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 111 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 111 173
  (Polychromatic418967fa.accept_9_8_3_2_1_417 35 111 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 111 173 (accept_3_2 34 111 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 111 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 111 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 111 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 111 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 173 (accept_3_2 31 111 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 111 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 111 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 111 173
  (Polychromatic418967fa.accept_7_1_6_5_1_39 29 111 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 111 173 (accept_3_2 28 111 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 111 173 (Polychromatic418967fa.accept_17_10_9_3_1_7144 27 111 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 111 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 111 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 173 (accept_3_2 25 111 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 111 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 111 173
  (Polychromatic418967fa.accept_9_5_3_2_1_171 23 111 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 111 173 (accept_3_2 22 111 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 111 173 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 111 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 111 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 111 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 173 (accept_3_2 19 111 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 111 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 173
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 111 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 111 173 (accept_3_2 16 111 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 111 173 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 111 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 111 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 111 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 173 (accept_3_2 13 111 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 173 (Polychromatic418967fa.accept_10_2_1_3_1_233 12 111 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 173
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 111 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 111 173 (accept_3_2 10 111 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  111 173 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 111 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 111 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 111 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 173 (accept_3_2 7 111 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 111 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 173
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 111 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 111 173 (accept_3_2 4 111 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  111 173 (Polychromatic418967fa.accept_13_3_7_4_1_435 3 111 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 111 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 111 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 173 (accept_3_2 1 111 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 111 173))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64
  110 173 (Eq.refl Bool.true) (allA_succ_of_accept 63 110 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 110 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 110 173
  (Polychromatic418967fa.accept_13_10_6_4_1_1583 62 110 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 110 173 (accept_3_2 61 110 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 110 173 (Polychromatic418967fa.accept_27_6_2_11_1_9778 60 110 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 110 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 110 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 110 173 (accept_3_2 58 110 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 110 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 110 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 110 173
  (Polychromatic418967fa.accept_12_8_2_5_1_844 56 110 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 110 173 (accept_3_2 55 110 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 110 173 (Polychromatic418967fa.accept_13_2_6_4_1_1593 54 110 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 110 173 (Polychromatic418967fa.accept_18_17_2_11_1_9749 53 110 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 110 173 (accept_3_2 52 110 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 110 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 110 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 110 173
  (Polychromatic418967fa.accept_13_11_6_4_1_3121 50 110 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 110 173 (accept_3_2 49 110 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 110 173 (Polychromatic418967fa.accept_13_9_6_4_1_2243 48 110 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 110 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 110 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 110 173 (accept_3_2 46 110 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 110 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 110 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 110 173
  (Polychromatic418967fa.accept_12_8_2_5_1_844 44 110 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 110 173 (accept_3_2 43 110 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 110 173 (Polychromatic418967fa.accept_15_12_5_8_1_5247 42 110 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 110 173 (Polychromatic418967fa.accept_13_2_6_4_1_1593 41 110 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 110 173 (accept_3_2 40 110 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 110 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 110 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 110 173
  (Polychromatic418967fa.accept_14_10_12_5_1_3466 38 110 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 110 173 (accept_3_2 37 110 173 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 110 173 (Polychromatic418967fa.accept_13_10_6_4_1_1583 36 110 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 110 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 110 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 110 173 (accept_3_2 34 110 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 110 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 33
  110 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 110 173
  (Polychromatic418967fa.accept_12_8_2_5_1_844 32 110 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 110 173 (accept_3_2 31 110 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 110 173 (Polychromatic418967fa.accept_17_13_8_3_1_7177 30 110 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 110 173 (Polychromatic418967fa.accept_15_14_5_8_1_3175 29 110 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 110 173 (accept_3_2 28 110 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 110 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 110 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 110 173
  (Polychromatic418967fa.accept_15_11_5_8_1_3157 26 110 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 110 173 (accept_3_2 25 110 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 110 173 (Polychromatic418967fa.accept_13_11_6_4_1_3121 24 110 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 110 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 110 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 110 173 (accept_3_2 22 110 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 110 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 110 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 110 173
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 110 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 110 173 (accept_3_2 19 110 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 110 173 (Polychromatic418967fa.accept_13_5_6_4_1_1582 18 110 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 110 173 (Polychromatic418967fa.accept_14_3_12_5_1_153 17 110 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 110 173 (accept_3_2 16 110 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 110 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 110 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 110 173
  (Polychromatic418967fa.accept_15_14_5_8_1_3175 14 110 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 110 173 (accept_3_2 13 110 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 110 173 (Polychromatic418967fa.accept_15_12_5_8_1_5247 12 110 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 110 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 110 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 110 173 (accept_3_2 10 110 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 110 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 110 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 110 173
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 110 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 110 173 (accept_3_2 7 110 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  110 173 (Polychromatic418967fa.accept_19_6_15_2_1_2857 6 110 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 110 173 (Polychromatic418967fa.accept_13_5_6_4_1_1582 5 110 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 110 173 (accept_3_2 4 110 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 110 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 110 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 110 173
  (Polychromatic418967fa.accept_13_2_6_4_1_1593 2 110 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 110 173 (accept_3_2 1 110 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  173)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 109 173 (Eq.refl Bool.true)
  (allA_of_3_0 65 109 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 66 108 173 (Eq.refl Bool.true)
  (allA_succ_of_accept 65 108 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 65 108 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 108 173 (accept_3_2 64 108 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 108 173 (Polychromatic418967fa.accept_16_15_12_13_1_1045 63 108 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 108 173
  (Polychromatic418967fa.accept_29_4_21_28_1_9777 62 108 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 108 173 (accept_3_2 61 108 173 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 108 173 (Polychromatic418967fa.accept_17_9_6_3_1_2398 60 108 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 108 173 (Polychromatic418967fa.accept_25_9_8_23_1_7913 59 108
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 108 173 (accept_3_2 58 108
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 108 173
  (Polychromatic418967fa.accept_7_1_3_5_1_33 57 108 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 108 173 (Polychromatic418967fa.accept_10_6_8_3_1_930 56 108 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 108 173 (accept_3_2 55 108 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 108 173 (Polychromatic418967fa.accept_11_10_9_8_1_1974 54 108 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 108 173
  (Polychromatic418967fa.accept_19_15_13_2_1_6851 53 108 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 108 173 (accept_3_2 52 108 173 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 108 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 108 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 108 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 50 108 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 108 173 (accept_3_2 49 108 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 108 173
  (Polychromatic418967fa.accept_17_14_6_3_1_2362 48 108 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 108 173 (Polychromatic418967fa.accept_16_15_12_13_1_1045 47 108 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 108 173 (accept_3_2 46 108 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 108 173 (Polychromatic418967fa.accept_10_5_8_3_1_229 45 108 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 108 173
  (Polychromatic418967fa.accept_7_2_3_5_1_34 44 108 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 108 173 (accept_3_2 43 108 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 108 173 (Polychromatic418967fa.accept_15_12_3_8_1_5245 42 108 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 108 173 (Polychromatic418967fa.accept_8_1_4_5_1_48 41 108 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 108 173 (accept_3_2 40 108 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 108 173 (Polychromatic418967fa.accept_15_9_3_8_1_3155 39 108 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 108 173
  (Polychromatic418967fa.accept_20_18_8_13_1_6761 38 108 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 108 173 (accept_3_2 37 108 173 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 108 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 108 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 108 173 (Polychromatic418967fa.accept_10_5_8_3_1_229 35 108
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 108 173 (accept_3_2 34 108
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 108 173
  (Polychromatic418967fa.accept_8_1_4_5_1_48 33 108 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 108 173 (Polychromatic418967fa.accept_11_10_9_8_1_1974 32 108 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 108 173 (accept_3_2 31 108 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 108 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 108 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 108 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 29
  108 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 108 173 (accept_3_2 28
  108 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 108 173
  (Polychromatic418967fa.accept_15_12_3_8_1_5245 27 108 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 108 173 (Polychromatic418967fa.accept_10_6_8_3_1_930 26 108 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 108 173 (accept_3_2 25 108 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 108 173 (Polychromatic418967fa.accept_15_9_3_8_1_3155 24 108 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 108 173
  (Polychromatic418967fa.accept_7_2_3_5_1_34 23 108 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 108 173 (accept_3_2 22 108 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 108 173 (Polychromatic418967fa.accept_10_1_8_3_1_947 21 108 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 108 173 (Polychromatic418967fa.accept_15_5_3_8_1_748 20 108 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 108 173 (accept_3_2 19 108 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 108 173 (Polychromatic418967fa.accept_17_1_6_3_1_4700 18 108
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 108 173
  (Polychromatic418967fa.accept_8_1_4_5_1_48 17 108 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 108 173 (accept_3_2 16 108 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 108 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 108 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 108 173 (Polychromatic418967fa.accept_17_14_6_3_1_2362 14 108 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 108 173 (accept_3_2 13 108 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 108 173 (Polychromatic418967fa.accept_14_12_10_5_1_2712 12 108
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 108 173
  (Polychromatic418967fa.accept_10_1_8_3_1_947 11 108 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 108 173 (accept_3_2 10 108 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  108 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 108 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 108 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 108 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 108 173 (accept_3_2 7 108 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 108 173 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 108 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 108 173
  (Polychromatic418967fa.accept_10_5_8_3_1_229 5 108 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 108 173 (accept_3_2 4 108 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  108 173 (Polychromatic418967fa.accept_20_3_8_13_1_3832 3 108 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 108 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 108 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 108 173 (accept_3_2 1 108 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 108 173)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  67 107 173 (Eq.refl Bool.true) (allA_succ_of_accept 66 107 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 107 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 107 173
  (Polychromatic418967fa.accept_10_5_7_3_1_561 65 107 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 107 173 (accept_3_2 64 107 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 107 173 (Polychromatic418967fa.accept_14_7_9_5_1_529 63 107 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 107 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 107 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 107 173 (accept_3_2 61 107 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 107 173 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 107 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 107 173
  (Polychromatic418967fa.accept_7_3_2_5_1_147 59 107 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 107 173 (accept_3_2 58 107 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 107 173 (Polychromatic418967fa.accept_9_3_8_2_1_162 57 107 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 107 173 (Polychromatic418967fa.accept_10_6_7_3_1_547 56 107 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 107 173 (accept_3_2 55 107 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 107 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 107 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 107 173
  (Polychromatic418967fa.accept_7_4_2_5_1_527 53 107 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 107 173 (accept_3_2 52 107 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 107 173 (Polychromatic418967fa.accept_9_6_8_2_1_410 51 107 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 107 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 107 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 107 173 (accept_3_2 49 107 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 107 173 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 107 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 107 173
  (Polychromatic418967fa.accept_19_9_12_2_1_9776 47 107 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 107 173 (accept_3_2 46 107 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 107 173 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 107 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 107 173 (Polychromatic418967fa.accept_10_4_7_3_1_54 44 107 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 107 173 (accept_3_2 43 107 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 107 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 107 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 107 173
  (Polychromatic418967fa.accept_9_5_8_2_1_409 41 107 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 107 173 (accept_3_2 40 107 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 107 173 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 107 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 107 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 107 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 107 173 (accept_3_2 37 107 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 107 173 (Polychromatic418967fa.accept_10_6_7_3_1_547 36 107 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 107 173
  (Polychromatic418967fa.accept_10_5_7_3_1_561 35 107 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 107 173 (accept_3_2 34 107 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 107 173 (Polychromatic418967fa.accept_9_6_8_2_1_410 33 107 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 107 173 (Polychromatic418967fa.accept_7_4_2_5_1_527 32 107 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 107 173 (accept_3_2 31 107 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 107 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 107 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 107 173
  (Polychromatic418967fa.accept_19_10_12_2_1_6948 29 107 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 107 173 (accept_3_2 28 107 173 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 107 173 (Polychromatic418967fa.accept_13_1_3_4_1_925 27 107 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 107 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 107 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 107 173 (accept_3_2 25 107 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 107 173 (Polychromatic418967fa.accept_7_3_2_5_1_147
  24 107 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 107 173
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 107 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 107 173 (accept_3_2 22 107 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 107 173 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 107 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 107 173 (Polychromatic418967fa.accept_13_7_3_4_1_459 20 107 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 107 173 (accept_3_2 19 107 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 107 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 107 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 107 173
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 107 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 107 173 (accept_3_2 16 107 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 107 173 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 107 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 107 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 107 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 107 173 (accept_3_2 13 107 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 107 173 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 107 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 107 173
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 107 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 107 173 (accept_3_2 10 107 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  107 173 (Polychromatic418967fa.accept_15_9_2_8_1_1379 9 107 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 107 173 (Polychromatic418967fa.accept_16_8_11_13_1_7265 8 107 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 107 173 (accept_3_2 7 107 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 107 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 107 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 107 173
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 107 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 107 173 (accept_3_2 4 107 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  107 173 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 107 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 107 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 107 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 107 173 (accept_3_2 1 107 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 107 173))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  68 106 173 (Eq.refl Bool.true) (allA_of_3_0 68 106 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 69 105 173
  (Eq.refl Bool.true) (allA_succ_of_accept 68 105 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 105 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 105 173 (accept_3_2 67 105 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 105 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 105 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 105 173
  (Polychromatic418967fa.accept_14_9_7_5_1_1105 65 105 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 105 173 (accept_3_2 64 105 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 105 173 (Polychromatic418967fa.accept_12_3_9_5_1_853 63 105 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 105 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 105 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 173 (accept_3_2 61 105 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 105 173 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 105 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 105 173
  (Polychromatic418967fa.accept_9_5_6_2_1_161 59 105 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 105 173 (accept_3_2 58 105 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 105 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 105 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 105 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 105 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 105 173 (accept_3_2 55 105 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 105 173 (Polychromatic418967fa.accept_14_12_7_5_1_1107 54 105 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 105 173
  (Polychromatic418967fa.accept_9_8_6_2_1_744 53 105 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 105 173 (accept_3_2 52 105 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 105 173 (Polychromatic418967fa.accept_12_3_9_5_1_853 51 105 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 105 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 105 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 105 173 (accept_3_2 49 105 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 105 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 105 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 105 173
  (Polychromatic418967fa.accept_10_7_5_3_1_542 47 105 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 105 173 (accept_3_2 46 105 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 105 173 (Polychromatic418967fa.accept_18_9_15_11_1_5693 45 105 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 105 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 105 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 173 (accept_3_2 43 105 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 105 173 (Polychromatic418967fa.accept_10_2_5_3_1_1408 42 105 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 105 173
  (Polychromatic418967fa.accept_9_5_6_2_1_161 41 105 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 105 173 (accept_3_2 40 105 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 105 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 105 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 105 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 105 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 173 (accept_3_2 37 105 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 105 173 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 105 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 105 173
  (Polychromatic418967fa.accept_9_8_6_2_1_744 35 105 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 105 173 (accept_3_2 34 105 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 105 173 (Polychromatic418967fa.accept_16_1_9_13_1_1822 33 105 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 105 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 105 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 173 (accept_3_2 31 105 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 105 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 105 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 105 173
  (Polychromatic418967fa.accept_13_3_1_4_1_945 29 105 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 105 173 (accept_3_2 28 105 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 105 173 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 105 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 105 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 105 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 173 (accept_3_2 25 105 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 105 173 (Polychromatic418967fa.accept_18_6_15_11_1_3141 24 105 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 105 173
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 105 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 105 173 (accept_3_2 22 105 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 105 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 105 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 105 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 105 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 173 (accept_3_2 19 105 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 173 (Polychromatic418967fa.accept_10_8_5_3_1_543 18 105 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 173
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 105 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 105 173 (accept_3_2 16 105 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 105 173 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 105 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 105 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 105 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 173 (accept_3_2 13 105 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 173 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 105 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 173
  (Polychromatic418967fa.accept_19_11_10_2_1_9757 11 105 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 105 173 (accept_3_2 10 105 173 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 105 173 (Polychromatic418967fa.accept_14_9_7_5_1_1105 9 105 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 105 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 105 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 173 (accept_3_2 7 105 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 105 173 (Polychromatic418967fa.accept_16_6_9_13_1_2751
  6 105 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 105 173
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 105 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 105 173 (accept_3_2 4 105 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  105 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 105 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 105 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 105 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 173 (accept_3_2 1 105 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 105 173)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 70 104 173 (Eq.refl Bool.true) (allA_succ_of_accept 69 104 173 (Polychromatic418967fa.accept_6_3_2_5_1_32
  69 104 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 104 173
  (Polychromatic418967fa.accept_11_2_5_8_1_470 68 104 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 104 173 (accept_3_2 67 104 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 104 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 66 104 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 104 173 (Polychromatic418967fa.accept_15_5_14_8_1_1376 65 104 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 104 173 (accept_3_2 64 104 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 104 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 104 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 104 173
  (Polychromatic418967fa.accept_9_8_5_2_1_422 62 104 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 104 173 (accept_3_2 61 104 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 104 173 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 104 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 104 173 (Polychromatic418967fa.accept_10_9_4_3_1_539 59 104 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 104 173 (accept_3_2 58 104 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 104 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 104 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 104 173
  (Polychromatic418967fa.accept_17_5_2_3_1_9775 56 104 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 104 173 (accept_3_2 55 104 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 104 173 (Polychromatic418967fa.accept_15_9_14_8_1_1396 54 104 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 104 173 (Polychromatic418967fa.accept_7_4_6_5_1_141 53 104 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 104 173 (accept_3_2 52 104 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 104 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 104 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 104 173
  (Polychromatic418967fa.accept_7_1_6_5_1_39 50 104 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 104 173 (accept_3_2 49 104 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 104 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 104 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 104 173 (Polychromatic418967fa.accept_10_7_4_3_1_560 47 104 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 104 173 (accept_3_2 46 104 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 104 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 104 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 104 173
  (Polychromatic418967fa.accept_9_8_5_2_1_422 44 104 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 104 173 (accept_3_2 43 104 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 104 173 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 104 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 104 173 (Polychromatic418967fa.accept_14_13_6_5_1_1853 41 104 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 104 173 (accept_3_2 40 104 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 104 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 104 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 104 173
  (Polychromatic418967fa.accept_12_2_8_5_1_408 38 104 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 104 173 (accept_3_2 37 104 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 104 173 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 104 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 104 173 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 104 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 104 173 (accept_3_2 34 104 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 104 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 104 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 104 173
  (Polychromatic418967fa.accept_7_4_6_5_1_141 32 104 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 104 173 (accept_3_2 31 104 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 104 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 104 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 104 173 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 104 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 104 173 (accept_3_2 28 104 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 104 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 104 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 104 173
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 104 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 104 173 (accept_3_2 25 104 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 104 173 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 104 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 104 173 (Polychromatic418967fa.accept_18_5_14_11_1_2073 23 104 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 104 173 (accept_3_2 22 104 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 104 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 104 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 104 173
  (Polychromatic418967fa.accept_15_5_14_8_1_1376 20 104 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 104 173 (accept_3_2 19 104 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 104 173 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 104 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 104 173 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 104 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 104 173 (accept_3_2 16 104 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 104 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 104 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 104 173
  (Polychromatic418967fa.accept_11_3_5_8_1_458 14 104 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 104 173 (accept_3_2 13 104 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 104 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 104 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 104 173 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 104 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 104 173 (accept_3_2 10 104 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 104 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 104 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 104 173
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 104 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 104 173 (accept_3_2 7 104 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  104 173 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 104 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 104 173 (Polychromatic418967fa.accept_15_5_14_8_1_1376 5 104 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 104 173 (accept_3_2 4 104 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 104 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 104 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 104 173
  (Polychromatic418967fa.accept_11_2_5_8_1_470 2 104 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 104 173 (accept_3_2 1 104 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  173)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 103 173 (Eq.refl Bool.true)
  (allA_of_3_0 71 103 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 72 102 173 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 102 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 102 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 102 173 (accept_3_2 70 102 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 102 173 (Polychromatic418967fa.accept_7_6_4_5_1_314 69 102 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 102 173 (Polychromatic418967fa.accept_9_5_3_2_1_171
  68 102 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 102 173 (accept_3_2 67
  102 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 102 173
  (Polychromatic418967fa.accept_19_9_7_2_1_6868 66 102 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 102 173 (Polychromatic418967fa.accept_7_2_4_5_1_313 65 102 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 102 173 (accept_3_2 64 102 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 102 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 102 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 102 173 (Polychromatic418967fa.accept_7_6_4_5_1_314
  62 102 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 102 173 (accept_3_2 61
  102 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 102 173
  (Polychromatic418967fa.accept_9_6_3_2_1_431 60 102 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 102 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 102 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 102 173 (accept_3_2 58 102 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 102 173 (Polychromatic418967fa.accept_7_1_4_5_1_35 57 102 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 102 173
  (Polychromatic418967fa.accept_15_11_12_8_1_739 56 102 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 102 173 (accept_3_2 55 102 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 102 173 (Polychromatic418967fa.accept_13_2_11_4_1_445 54 102 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 102 173 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 102 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 102 173 (accept_3_2 52 102 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 102 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 102 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 102 173
  (Polychromatic418967fa.accept_7_1_4_5_1_35 50 102 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 102 173 (accept_3_2 49 102 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 102 173 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 102 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 102 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 102 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 102 173 (accept_3_2 46 102 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 102 173 (Polychromatic418967fa.accept_10_5_2_3_1_239 45 102 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 102 173
  (Polychromatic418967fa.accept_7_2_4_5_1_313 44 102 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 102 173 (accept_3_2 43 102 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 102 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 102 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 102 173 (Polychromatic418967fa.accept_7_6_4_5_1_314 41 102 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 102 173 (accept_3_2 40 102 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 102 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 102 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 102 173
  (Polychromatic418967fa.accept_11_5_3_8_1_454 38 102 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 102 173 (accept_3_2 37 102 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 102 173 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 102 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 102 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 102 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 102 173 (accept_3_2 34 102 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 102 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 102 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 102 173
  (Polychromatic418967fa.accept_9_5_3_2_1_171 32 102 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 102 173 (accept_3_2 31 102 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 102 173 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 102 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 102 173 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 102 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 102 173 (accept_3_2 28 102 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 102 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 102 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 102 173
  (Polychromatic418967fa.accept_9_8_3_2_1_417 26 102 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 102 173 (accept_3_2 25 102 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 102 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 102 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 102 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 102 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 102 173 (accept_3_2 22 102 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 102 173 (Polychromatic418967fa.accept_10_1_2_3_1_1910 21 102 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 102 173
  (Polychromatic418967fa.accept_7_6_4_5_1_314 20 102 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 102 173 (accept_3_2 19 102 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 102 173 (Polychromatic418967fa.accept_15_3_12_8_1_738 18 102 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 102 173 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 102 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 102 173 (accept_3_2 16 102 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 102 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 102 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 102 173
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 102 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 102 173 (accept_3_2 13 102 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 102 173 (Polychromatic418967fa.accept_13_12_11_4_1_3111 12 102 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 102 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 102 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 102 173 (accept_3_2 10 102 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 102 173 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 102 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 102 173
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 102 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 102 173 (accept_3_2 7 102 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  102 173 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 102 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 102 173 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 102 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 102 173 (accept_3_2 4 102 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 102 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 102 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 102 173
  (Polychromatic418967fa.accept_7_2_4_5_1_313 2 102 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 102 173 (accept_3_2 1 102 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  173)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 101 173 (Eq.refl Bool.true)
  (allA_succ_of_accept 72 101 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 72 101 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 101 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 71 101 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 101 173 (accept_3_2 70 101 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 101 173
  (Polychromatic418967fa.accept_19_12_6_2_1_5424 69 101 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 101 173 (Polychromatic418967fa.accept_10_8_1_3_1_1374 68 101 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 101 173 (accept_3_2 67 101 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 101 173 (Polychromatic418967fa.accept_13_1_10_4_1_954 66 101 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 101 173
  (Polychromatic418967fa.accept_7_2_3_5_1_34 65 101 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 101 173 (accept_3_2 64 101 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 101 173 (Polychromatic418967fa.accept_13_11_10_4_1_1565 63 101 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 101 173 (Polychromatic418967fa.accept_10_2_1_3_1_233 62 101 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 101 173 (accept_3_2 61 101 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 101 173 (Polychromatic418967fa.accept_11_5_2_8_1_866 60 101
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 101 173
  (Polychromatic418967fa.accept_13_7_10_4_1_919 59 101 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 101 173 (accept_3_2 58 101 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 101 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 101 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 101 173 (Polychromatic418967fa.accept_16_8_5_13_1_1021 56 101 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 101 173 (accept_3_2 55 101 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 101 173 (Polychromatic418967fa.accept_14_12_3_5_1_1868 54 101
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 101 173
  (Polychromatic418967fa.accept_13_1_10_4_1_954 53 101 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 101 173 (accept_3_2 52 101 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 101 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 101 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 101 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 50 101 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 101 173 (accept_3_2 49 101 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 101 173 (Polychromatic418967fa.accept_10_8_1_3_1_1374 48 101 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 101 173
  (Polychromatic418967fa.accept_13_8_10_4_1_2270 47 101 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 101 173 (accept_3_2 46 101 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 101 173 (Polychromatic418967fa.accept_13_6_10_4_1_957 45 101 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 101 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 44 101 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 101 173 (accept_3_2 43 101 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 101 173 (Polychromatic418967fa.accept_10_2_1_3_1_233 42 101 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 101 173
  (Polychromatic418967fa.accept_16_9_5_13_1_4972 41 101 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 101 173 (accept_3_2 40 101 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 101 173 (Polychromatic418967fa.accept_19_1_6_2_1_8341 39 101 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 101 173 (Polychromatic418967fa.accept_10_8_1_3_1_1374 38 101 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 101 173 (accept_3_2 37 101 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 101 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 101 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 101 173
  (Polychromatic418967fa.accept_15_5_11_8_1_1391 35 101 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 101 173 (accept_3_2 34 101 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 101 173 (Polychromatic418967fa.accept_13_7_10_4_1_919 33 101 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 101 173 (Polychromatic418967fa.accept_10_2_1_3_1_233 32 101 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 101 173 (accept_3_2 31 101 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 101 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 101 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 101 173
  (Polychromatic418967fa.accept_7_1_3_5_1_33 29 101 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 101 173 (accept_3_2 28 101 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 101 173 (Polychromatic418967fa.accept_11_5_2_8_1_866 27 101 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 101 173 (Polychromatic418967fa.accept_14_12_3_5_1_1868 26 101 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 101 173 (accept_3_2 25 101 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 101 173 (Polychromatic418967fa.accept_13_11_10_4_1_1565 24 101
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 101 173
  (Polychromatic418967fa.accept_7_2_3_5_1_34 23 101 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 101 173 (accept_3_2 22 101 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 101 173 (Polychromatic418967fa.accept_13_8_10_4_1_2270 21 101 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 101 173 (Polychromatic418967fa.accept_13_7_10_4_1_919 20 101 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 101 173 (accept_3_2 19 101 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 101 173 (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 101
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 101 173
  (Polychromatic418967fa.accept_16_1_5_13_1_1025 17 101 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 101 173 (accept_3_2 16 101 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 101 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 101 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 101 173 (Polychromatic418967fa.accept_13_1_10_4_1_954 14 101 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 101 173 (accept_3_2 13 101 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 101 173 (Polychromatic418967fa.accept_10_2_1_3_1_233 12 101
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 101 173
  (Polychromatic418967fa.accept_13_11_10_4_1_1565 11 101 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 101 173 (accept_3_2 10 101 173 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 101 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 101 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 101 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 101 173 (accept_3_2 7 101 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 101 173 (Polychromatic418967fa.accept_13_6_10_4_1_957
  6 101 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 101 173
  (Polychromatic418967fa.accept_11_5_2_8_1_866 5 101 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 101 173 (accept_3_2 4 101 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  101 173 (Polychromatic418967fa.accept_15_3_11_8_1_4186 3 101 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 101 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 101 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 101 173 (accept_3_2 1 101 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 101 173)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 74 100 173 (Eq.refl Bool.true) (allA_of_3_0 74 100 173 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 75 99 173 (Eq.refl Bool.true) (allA_succ_of_accept 74 99 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 74
  99 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 99 173 (accept_3_2 73 99
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 99 173
  (Polychromatic418967fa.accept_16_8_3_13_1_7295 72 99 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 99 173 (Polychromatic418967fa.accept_19_14_4_2_1_2840 71 99 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 173 (accept_3_2 70 99 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 99 173 (Polychromatic418967fa.accept_7_6_1_5_1_322 69 99 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 99 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 68
  99 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 99 173 (accept_3_2 67 99
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 99 173 (Polychromatic418967fa.accept_4_2_3_1_1_2
  66 99 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 99 173
  (Polychromatic418967fa.accept_16_1_3_13_1_2785 65 99 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 99 173 (accept_3_2 64 99 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  99 173 (Polychromatic418967fa.accept_13_11_8_4_1_3950 63 99 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 99 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 99 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 99 173 (accept_3_2 61 99 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 99 173 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 99 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 99 173
  (Polychromatic418967fa.accept_7_3_1_5_1_44 59 99 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 99 173 (accept_3_2 58 99 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  99 173 (Polychromatic418967fa.accept_12_9_3_5_1_423 57 99 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 99 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 99 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 99 173 (accept_3_2 55 99 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 99 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 99 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 99 173
  (Polychromatic418967fa.accept_7_4_1_5_1_540 53 99 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 99 173 (accept_3_2 52 99 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  99 173 (Polychromatic418967fa.accept_13_12_8_4_1_3099 51 99 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 99 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 99 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 99 173 (accept_3_2 49 99 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 99 173 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 99 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 99 173
  (Polychromatic418967fa.accept_15_2_9_8_1_736 47 99 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 99 173 (accept_3_2 46 99 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  99 173 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 99 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 99 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 99 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 99 173 (accept_3_2 43 99 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 99 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 99 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 99 173
  (Polychromatic418967fa.accept_7_6_1_5_1_322 41 99 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 99 173 (accept_3_2 40 99 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  99 173 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 99 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 99 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 99 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 99 173 (accept_3_2 37 99 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 99 173 (Polychromatic418967fa.accept_10_6_9_3_1_935 36 99 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 99 173
  (Polychromatic418967fa.accept_13_9_8_4_1_937 35 99 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 99 173 (accept_3_2 34 99 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  99 173 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 99 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 99 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 99 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 173 (accept_3_2 31 99 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 99 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 99 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 173
  (Polychromatic418967fa.accept_15_14_9_8_1_3165 29 99 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 99 173 (accept_3_2 28 99 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  99 173 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 99 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 99 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 99 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 173 (accept_3_2 25 99 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 99 173 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 99 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 99 173
  (Polychromatic418967fa.accept_13_10_8_4_1_3098 23 99 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 99 173 (accept_3_2 22 99 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  99 173 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 99 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 99 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 99 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 99 173 (accept_3_2 19 99 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 99 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 99 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 173
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 99 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 99 173 (accept_3_2 16 99 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  99 173 (Polychromatic418967fa.accept_16_15_3_13_1_2818 15 99 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 99 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 99 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 173 (accept_3_2 13 99 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 99 173 (Polychromatic418967fa.accept_13_12_8_4_1_3099 12 99 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 99 173
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 99 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 99 173 (accept_3_2 10 99 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  99 173 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 99 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 99 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 99 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 173 (accept_3_2 7 99 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 99 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 99 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 173
  (Polychromatic418967fa.accept_19_5_4_2_1_6840 5 99 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 99 173 (accept_3_2 4 99 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99
  173 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 99 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 99 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 99 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 173 (accept_3_2 1 99 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 99 173))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76
  98 173 (Eq.refl Bool.true) (allA_succ_of_accept 75 98 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 98 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 98 173
  (Polychromatic418967fa.accept_13_9_7_4_1_953 74 98 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 98 173 (accept_3_2 73 98 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  98 173 (Polychromatic418967fa.accept_17_4_13_3_1_7166 72 98 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 98 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 98 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 98 173 (accept_3_2 70 98 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 98 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 98 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 98 173
  (Polychromatic418967fa.accept_9_5_8_2_1_409 68 98 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 98 173 (accept_3_2 67 98 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  98 173 (Polychromatic418967fa.accept_9_3_8_2_1_162 66 98 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 98 173 (Polychromatic418967fa.accept_10_5_8_3_1_229 65 98 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 98 173 (accept_3_2 64 98 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 98 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 98 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 98 173
  (Polychromatic418967fa.accept_13_10_7_4_1_2262 62 98 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 98 173 (accept_3_2 61 98 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  98 173 (Polychromatic418967fa.accept_9_6_8_2_1_410 60 98 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 98 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 98 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 98 173 (accept_3_2 58 98 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 98 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 98 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 98 173
  (Polychromatic418967fa.accept_10_6_8_3_1_930 56 98 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 98 173 (accept_3_2 55 98 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  98 173 (Polychromatic418967fa.accept_19_16_3_2_1_6964 54 98 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 98 173 (Polychromatic418967fa.accept_11_9_10_8_1_444 53 98 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 98 173 (accept_3_2 52 98 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 98 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 98 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 98 173
  (Polychromatic418967fa.accept_9_5_8_2_1_409 50 98 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 98 173 (accept_3_2 49 98 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  98 173 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 98 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 98 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 98 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 98 173 (accept_3_2 46 98 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 98 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 98 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 98 173
  (Polychromatic418967fa.accept_12_8_2_5_1_844 44 98 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 98 173 (accept_3_2 43 98 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  98 173 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 98 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 98 173 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 98 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 98 173 (accept_3_2 40 98 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 98 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 98 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 98 173
  (Polychromatic418967fa.accept_13_12_7_4_1_3124 38 98 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 98 173 (accept_3_2 37 98 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  98 173 (Polychromatic418967fa.accept_10_6_8_3_1_930 36 98 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 98 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 98 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 98 173 (accept_3_2 34 98 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 98 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 98 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 98 173
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 98 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 98 173 (accept_3_2 31 98 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  98 173 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 98 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 98 173 (Polychromatic418967fa.accept_13_3_7_4_1_435 29 98 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 98 173 (accept_3_2 28 98 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 98 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 98 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 98 173
  (Polychromatic418967fa.accept_10_6_8_3_1_930 26 98 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 98 173 (accept_3_2 25 98 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  98 173 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 98 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 98 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 98 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 98 173 (accept_3_2 22 98 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 98 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 98 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 98 173
  (Polychromatic418967fa.accept_11_9_10_8_1_444 20 98 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 98 173 (accept_3_2 19 98 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  98 173 (Polychromatic418967fa.accept_19_18_3_2_1_6939 18 98 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 98 173 (Polychromatic418967fa.accept_19_17_3_2_1_1725 17 98 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 98 173 (accept_3_2 16 98 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 98 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 98 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 98 173
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 98 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 98 173 (accept_3_2 13 98 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  98 173 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 98 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 98 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 98 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 98 173 (accept_3_2 10 98 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 98 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 98 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 98 173
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 98 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 98 173 (accept_3_2 7 98 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 98
  173 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 98 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 98 173 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 98 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 98 173 (accept_3_2 4 98 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 98 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 98 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 98 173 (Polychromatic418967fa.accept_20_2_18_13_1_3843
  2 98 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 98 173 (accept_3_2 1 98
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  173)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 97 173 (Eq.refl
  Bool.true) (allA_of_3_0 77 97 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 78 96 173 (Eq.refl Bool.true)
  (allA_succ_of_accept 77 96 173 (Polychromatic418967fa.accept_9_5_6_2_1_161 77 96 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 96 173 (accept_3_2 76 96 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 96 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 75 96 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 96 173 (Polychromatic418967fa.accept_13_9_5_4_1_1591
  74 96 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 96 173 (accept_3_2 73
  96 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 96 173
  (Polychromatic418967fa.accept_19_15_1_2_1_6894 72 96 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 96 173 (Polychromatic418967fa.accept_9_8_6_2_1_744 71 96 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 96 173 (accept_3_2 70 96 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 96 173 (Polychromatic418967fa.accept_10_9_6_3_1_545 69 96 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 96 173 (Polychromatic418967fa.accept_9_5_6_2_1_161 68
  96 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 96 173 (accept_3_2 67 96
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 96 173
  (Polychromatic418967fa.accept_9_3_6_2_1_160 66 96 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 96 173 (Polychromatic418967fa.accept_17_14_11_3_1_4653 65 96 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 96 173 (accept_3_2 64 96 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 96 173 (Polychromatic418967fa.accept_14_7_12_5_1_1861 63 96 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 96 173
  (Polychromatic418967fa.accept_9_8_6_2_1_744 62 96 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 96 173 (accept_3_2 61 96 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  96 173 (Polychromatic418967fa.accept_17_9_11_3_1_2353 60 96 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 96 173 (Polychromatic418967fa.accept_9_5_6_2_1_161 59 96 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 96 173 (accept_3_2 58 96 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 96 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 96 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 96 173
  (Polychromatic418967fa.accept_19_18_1_2_1_5430 56 96 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 96 173 (accept_3_2 55 96 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  96 173 (Polychromatic418967fa.accept_13_2_5_4_1_3926 54 96 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 96 173 (Polychromatic418967fa.accept_9_8_6_2_1_744 53 96 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 96 173 (accept_3_2 52 96 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 96 173 (Polychromatic418967fa.accept_13_12_5_4_1_3133 51 96 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 96 173
  (Polychromatic418967fa.accept_9_5_6_2_1_161 50 96 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 96 173 (accept_3_2 49 96 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  96 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 96 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 96 173 (Polychromatic418967fa.accept_10_7_6_3_1_927 47 96 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 96 173 (accept_3_2 46 96 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 96 173 (Polychromatic418967fa.accept_13_6_5_4_1_3924 45 96 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 96 173
  (Polychromatic418967fa.accept_9_8_6_2_1_744 44 96 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 96 173 (accept_3_2 43 96 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  96 173 (Polychromatic418967fa.accept_22_20_8_19_1_9748 42 96 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 96 173 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 96 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 96 173 (accept_3_2 40 96 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 96 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 96 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 96 173
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 38 96 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 96 173 (accept_3_2 37 96 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  96 173 (Polychromatic418967fa.accept_13_10_5_4_1_3107 36 96 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 96 173 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 96 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 96 173 (accept_3_2 34 96 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 96 173 (Polychromatic418967fa.accept_18_15_6_11_1_5651 33 96 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 96 173
  (Polychromatic418967fa.accept_9_5_6_2_1_161 32 96 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 96 173 (accept_3_2 31 96 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  96 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 96 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 96 173 (Polychromatic418967fa.accept_10_9_6_3_1_545 29 96 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 96 173 (accept_3_2 28 96 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 96 173 (Polychromatic418967fa.accept_10_7_6_3_1_927 27 96 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 96 173
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 96 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 96 173 (accept_3_2 25 96 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  96 173 (Polychromatic418967fa.accept_14_10_12_5_1_3466 24 96 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 96 173 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 96 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 96 173 (accept_3_2 22 96 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 96 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 96 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 96 173
  (Polychromatic418967fa.accept_22_20_8_19_1_9748 20 96 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 96 173 (accept_3_2 19 96 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  96 173 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 96 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 96 173 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 96 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 96 173 (accept_3_2 16 96 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 96 173 (Polychromatic418967fa.accept_13_2_5_4_1_3926 15 96 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 96 173
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 96 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 96 173 (accept_3_2 13 96 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  96 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 96 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 96 173 (Polychromatic418967fa.accept_21_11_12_5_1_2224 11 96 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 96 173 (accept_3_2 10 96 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 96 173 (Polychromatic418967fa.accept_10_9_6_3_1_545 9 96 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 96 173
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 96 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 96 173 (accept_3_2 7 96 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 96
  173 (Polychromatic418967fa.accept_13_6_5_4_1_3924 6 96 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 96 173 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 96 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 96 173 (accept_3_2 4 96 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 96 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 96 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 96 173
  (Polychromatic418967fa.accept_13_2_5_4_1_3926 2 96 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 96 173 (accept_3_2 1 96 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  173)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 79 95 173 (Eq.refl
  Bool.true) (allA_succ_of_accept 78 95 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 95 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 95 173 (Polychromatic418967fa.accept_10_7_5_3_1_542
  77 95 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 95 173 (accept_3_2 76
  95 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 95 173
  (Polychromatic418967fa.accept_9_3_5_2_1_28 75 95 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 95 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 95 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 95 173 (accept_3_2 73 95 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 95 173 (Polychromatic418967fa.accept_7_2_4_5_1_313 72 95 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 173 (Polychromatic418967fa.accept_7_1_4_5_1_35 71
  95 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 95 173 (accept_3_2 70 95
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 95 173
  (Polychromatic418967fa.accept_7_6_4_5_1_314 69 95 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 95 173 (Polychromatic418967fa.accept_10_8_5_3_1_543 68 95 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 95 173 (accept_3_2 67 95 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 95 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 95 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 95 173 (Polychromatic418967fa.accept_7_2_4_5_1_313 65
  95 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 95 173 (accept_3_2 64 95
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 95 173
  (Polychromatic418967fa.accept_15_3_5_8_1_1387 63 95 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 95 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 95 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 173 (accept_3_2 61 95 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 95 173 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 95 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 95 173 (Polychromatic418967fa.accept_11_4_7_8_1_1926
  59 95 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 95 173 (accept_3_2 58
  95 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 95 173
  (Polychromatic418967fa.accept_7_1_4_5_1_35 57 95 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 95 173 (Polychromatic418967fa.accept_15_11_5_8_1_3157 56 95 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 95 173 (accept_3_2 55 95 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 95 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 95 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 173 (Polychromatic418967fa.accept_9_8_5_2_1_422 53
  95 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 95 173 (accept_3_2 52 95
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 95 173
  (Polychromatic418967fa.accept_7_2_4_5_1_313 51 95 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 95 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 95 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 95 173 (accept_3_2 49 95 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 95 173 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 95 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 95 173 (Polychromatic418967fa.accept_10_7_5_3_1_542
  47 95 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 95 173 (accept_3_2 46
  95 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 95 173
  (Polychromatic418967fa.accept_17_11_10_3_1_2364 45 95 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 95 173 (Polychromatic418967fa.accept_7_2_4_5_1_313 44 95 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 173 (accept_3_2 43 95 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 95 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 95 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 173 (Polychromatic418967fa.accept_7_6_4_5_1_314 41
  95 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 95 173 (accept_3_2 40 95
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 95 173 (Polychromatic418967fa.accept_9_3_5_2_1_28
  39 95 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 95 173
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 95 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 95 173 (accept_3_2 37 95 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  95 173 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 95 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 95 173 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 95 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 95 173 (accept_3_2 34 95 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 95 173 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 95 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 95 173
  (Polychromatic418967fa.accept_10_2_5_3_1_1408 32 95 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 95 173 (accept_3_2 31 95 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  95 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 95 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 95 173 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 95 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 95 173 (accept_3_2 28 95 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 95 173 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 95 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 95 173
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 95 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 95 173 (accept_3_2 25 95 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  95 173 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 95 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 95 173 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 95 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 95 173 (accept_3_2 22 95 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 95 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 95 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 95 173
  (Polychromatic418967fa.accept_7_6_4_5_1_314 20 95 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 95 173 (accept_3_2 19 95 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  95 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 95 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 95 173 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 95 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 95 173 (accept_3_2 16 95 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 95 173 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 95 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 95 173
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 95 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 95 173 (accept_3_2 13 95 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  95 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 95 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 95 173 (Polychromatic418967fa.accept_15_11_5_8_1_3157 11 95 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 95 173 (accept_3_2 10 95 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 95 173 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 95 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 95 173
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 95 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 95 173 (accept_3_2 7 95 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 95
  173 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 95 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 95 173 (Polychromatic418967fa.accept_20_5_15_13_1_5235 5 95 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 95 173 (accept_3_2 4 95 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 95 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 95 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 95 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 95
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 173 (accept_3_2 1 95 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 95
  173))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 94 173 (Eq.refl
  Bool.true) (allA_of_3_0 80 94 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 81 93 173 (Eq.refl Bool.true)
  (allA_succ_of_accept 80 93 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 93 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 93 173 (accept_3_2 79 93 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 93 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 78 93 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 93 173 (Polychromatic418967fa.accept_9_5_3_2_1_171 77
  93 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 173 (accept_3_2 76 93
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 93 173
  (Polychromatic418967fa.accept_12_3_9_5_1_853 75 93 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 93 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 93 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 93 173 (accept_3_2 73 93 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 93 173 (Polychromatic418967fa.accept_15_12_3_8_1_5245 72 93 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 93 173
  (Polychromatic418967fa.accept_9_8_3_2_1_417 71 93 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 93 173 (accept_3_2 70 93 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  93 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 69 93 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 93 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 93 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 93 173 (accept_3_2 67 93 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 93 173 (Polychromatic418967fa.accept_7_3_2_5_1_147 66 93 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 93 173
  (Polychromatic418967fa.accept_15_5_3_8_1_748 65 93 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 93 173 (accept_3_2 64 93 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  93 173 (Polychromatic418967fa.accept_12_3_9_5_1_853 63 93 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 93 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 93 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 93 173 (accept_3_2 61 93 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 93 173 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 93 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 93 173
  (Polychromatic418967fa.accept_7_3_2_5_1_147 59 93 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 93 173 (accept_3_2 58 93 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  93 173 (Polychromatic418967fa.accept_11_2_5_8_1_470 57 93 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 93 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 93 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 93 173 (accept_3_2 55 93 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 93 173 (Polychromatic418967fa.accept_15_9_3_8_1_3155 54 93 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 93 173
  (Polychromatic418967fa.accept_7_4_2_5_1_527 53 93 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 93 173 (accept_3_2 52 93 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  93 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 93 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 93 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 93 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 93 173 (accept_3_2 49 93 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 93 173 (Polychromatic418967fa.accept_19_10_17_2_1_5411 48 93 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 93 173
  (Polychromatic418967fa.accept_11_3_5_8_1_458 47 93 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 93 173 (accept_3_2 46 93 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  93 173 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 93 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 93 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 93 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 93 173 (accept_3_2 43 93 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 93 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 93 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 93 173
  (Polychromatic418967fa.accept_9_5_3_2_1_171 41 93 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 93 173 (accept_3_2 40 93 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  93 173 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 93 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 93 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 93 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 93 173 (accept_3_2 37 93 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 93 173 (Polychromatic418967fa.accept_11_3_5_8_1_458 36 93 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 93 173
  (Polychromatic418967fa.accept_9_8_3_2_1_417 35 93 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 93 173 (accept_3_2 34 93 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  93 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 93 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 93 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 93 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 93 173 (accept_3_2 31 93 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 93 173 (Polychromatic418967fa.accept_17_13_8_3_1_7177 30 93 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 93 173
  (Polychromatic418967fa.accept_17_12_8_3_1_4646 29 93 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 93 173 (accept_3_2 28 93 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  93 173 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 93 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 93 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 93 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 93 173 (accept_3_2 25 93 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 93 173 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 93 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 93 173
  (Polychromatic418967fa.accept_9_5_3_2_1_171 23 93 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 93 173 (accept_3_2 22 93 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  93 173 (Polychromatic418967fa.accept_14_7_9_5_1_529 21 93 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 93 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 93 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 173 (accept_3_2 19 93 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 93 173 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 93 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 173
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 93 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 93 173 (accept_3_2 16 93 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  93 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 93 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 93 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 93 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 173 (accept_3_2 13 93 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 93 173 (Polychromatic418967fa.accept_13_12_2_4_1_3131 12 93 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 173
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 93 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 93 173 (accept_3_2 10 93 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  93 173 (Polychromatic418967fa.accept_15_9_3_8_1_3155 9 93 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 93 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 93 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 173 (accept_3_2 7 93 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 93 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 93 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 173
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 93 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 93 173 (accept_3_2 4 93 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93
  173 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 93 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 93 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 93 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 173 (accept_3_2 1 93 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 93 173)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 82 92 173 (Eq.refl Bool.true) (allA_succ_of_accept 81 92 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 81
  92 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 92 173
  (Polychromatic418967fa.accept_7_3_1_5_1_44 80 92 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 92 173 (accept_3_2 79 92 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  92 173 (Polychromatic418967fa.accept_11_1_4_8_1_1918 78 92 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 92 173 (Polychromatic418967fa.accept_21_14_8_5_1_6586 77 92 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 92 173 (accept_3_2 76 92 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 92 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 92 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 92 173
  (Polychromatic418967fa.accept_7_4_1_5_1_540 74 92 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 92 173 (accept_3_2 73 92 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  92 173 (Polychromatic418967fa.accept_16_8_12_13_1_3851 72 92 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 92 173 (Polychromatic418967fa.accept_10_1_2_3_1_1910 71 92 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 92 173 (accept_3_2 70 92 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 92 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 92 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 92 173
  (Polychromatic418967fa.accept_13_3_1_4_1_945 68 92 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 92 173 (accept_3_2 67 92 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  92 173 (Polychromatic418967fa.accept_7_3_1_5_1_44 66 92 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 92 173 (Polychromatic418967fa.accept_8_1_4_5_1_48 65 92 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 92 173 (accept_3_2 64 92 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 92 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 92 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 92 173
  (Polychromatic418967fa.accept_7_6_1_5_1_322 62 92 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 92 173 (accept_3_2 61 92 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  92 173 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 92 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 92 173 (Polychromatic418967fa.accept_7_3_1_5_1_44 59 92 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 92 173 (accept_3_2 58 92 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 92 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 92 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 92 173
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 56 92 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 92 173 (accept_3_2 55 92 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  92 173 (Polychromatic418967fa.accept_15_9_2_8_1_1379 54 92 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 92 173 (Polychromatic418967fa.accept_7_4_1_5_1_540 53 92 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 92 173 (accept_3_2 52 92 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 92 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 92 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 92 173
  (Polychromatic418967fa.accept_12_2_8_5_1_408 50 92 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 92 173 (accept_3_2 49 92 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  92 173 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 92 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 92 173 (Polychromatic418967fa.accept_16_15_12_13_1_1045 47 92 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 92 173 (accept_3_2 46 92 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 92 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 92 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 92 173
  (Polychromatic418967fa.accept_13_5_1_4_1_3966 44 92 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 92 173 (accept_3_2 43 92 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  92 173 (Polychromatic418967fa.accept_13_3_1_4_1_945 42 92 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 92 173 (Polychromatic418967fa.accept_7_6_1_5_1_322 41 92 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 92 173 (accept_3_2 40 92 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 92 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 92 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 92 173
  (Polychromatic418967fa.accept_7_3_1_5_1_44 38 92 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 92 173 (accept_3_2 37 92 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  92 173 (Polychromatic418967fa.accept_13_10_1_4_1_3103 36 92 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 92 173 (Polychromatic418967fa.accept_10_5_2_3_1_239 35 92 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 92 173 (accept_3_2 34 92 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 92 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 92 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 92 173
  (Polychromatic418967fa.accept_7_4_1_5_1_540 32 92 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 92 173 (accept_3_2 31 92 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  92 173 (Polychromatic418967fa.accept_19_11_16_2_1_9759 30 92 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 92 173 (Polychromatic418967fa.accept_11_7_4_8_1_1371 29 92 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 92 173 (accept_3_2 28 92 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 92 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 92 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 92 173
  (Polychromatic418967fa.accept_12_2_8_5_1_408 26 92 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 92 173 (accept_3_2 25 92 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  92 173 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 92 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 92 173 (Polychromatic418967fa.accept_11_1_4_8_1_1918 23 92 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 92 173 (accept_3_2 22 92 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 92 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 92 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 92 173
  (Polychromatic418967fa.accept_7_6_1_5_1_322 20 92 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 92 173 (accept_3_2 19 92 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  92 173 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 92 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 92 173 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 92 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 92 173 (accept_3_2 16 92 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 92 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 92 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 92 173
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 92 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 92 173 (accept_3_2 13 92 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  92 173 (Polychromatic418967fa.accept_11_1_4_8_1_1918 12 92 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 92 173 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 92 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 92 173 (accept_3_2 10 92 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 92 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 92 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 92 173
  (Polychromatic418967fa.accept_16_8_12_13_1_3851 8 92 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 92 173 (accept_3_2 7 92 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 92
  173 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 92 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 92 173 (Polychromatic418967fa.accept_10_5_2_3_1_239 5 92 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 92 173 (accept_3_2 4 92 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 92 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 92 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 92 173 (Polychromatic418967fa.accept_12_2_8_5_1_408 2
  92 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 173 (accept_3_2 1 92 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  173)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 91 173 (Eq.refl
  Bool.true) (allA_of_3_0 83 91 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 84 90 173 (Eq.refl Bool.true)
  (allA_succ_of_accept 83 90 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 90 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 90 173 (accept_3_2 82 90 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 90 173 (Polychromatic418967fa.accept_7_4_6_5_1_141 81 90 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 90 173 (Polychromatic418967fa.accept_13_2_12_4_1_943
  80 90 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 90 173 (accept_3_2 79
  90 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 90 173
  (Polychromatic418967fa.accept_7_1_6_5_1_39 78 90 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 90 173 (Polychromatic418967fa.accept_19_1_14_2_1_4134 77 90 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 90 173 (accept_3_2 76 90 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 90 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 90 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 90 173 (Polychromatic418967fa.accept_7_4_6_5_1_141 74
  90 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 90 173 (accept_3_2 73 90
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 90 173
  (Polychromatic418967fa.accept_13_7_12_4_1_450 72 90 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 90 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 90 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 90 173 (accept_3_2 70 90 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 90 173 (Polychromatic418967fa.accept_14_13_6_5_1_1853 69 90 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 90 173
  (Polychromatic418967fa.accept_13_3_12_4_1_110 68 90 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 90 173 (accept_3_2 67 90 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  90 173 (Polychromatic418967fa.accept_21_3_6_5_1_8187 66 90 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 90 173 (Polychromatic418967fa.accept_19_8_14_2_1_9774 65 90 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 90 173 (accept_3_2 64 90 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 90 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 90 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 90 173
  (Polychromatic418967fa.accept_16_14_10_13_1_2768 62 90 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 90 173 (accept_3_2 61 90 173 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 90 173 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 90 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 90 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 90 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 90 173 (accept_3_2 58 90 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 90 173 (Polychromatic418967fa.accept_7_1_6_5_1_39 57
  90 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 90 173
  (Polychromatic418967fa.accept_22_12_2_19_1_9773 56 90 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 90 173 (accept_3_2 55 90 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  90 173 (Polychromatic418967fa.accept_13_2_12_4_1_943 54 90 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 90 173 (Polychromatic418967fa.accept_7_4_6_5_1_141 53 90 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 90 173 (accept_3_2 52 90 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 90 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 90 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 90 173
  (Polychromatic418967fa.accept_7_1_6_5_1_39 50 90 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 90 173 (accept_3_2 49 90 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  90 173 (Polychromatic418967fa.accept_23_2_21_12_1_9772 48 90 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 90 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 90 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 90 173 (accept_3_2 46 90 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 90 173 (Polychromatic418967fa.accept_19_7_14_2_1_4095 45 90 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 90 173
  (Polychromatic418967fa.accept_13_5_12_4_1_449 44 90 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 90 173 (accept_3_2 43 90 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  90 173 (Polychromatic418967fa.accept_13_3_12_4_1_110 42 90 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 90 173 (Polychromatic418967fa.accept_13_2_12_4_1_943 41 90 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 90 173 (accept_3_2 40 90 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 90 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 90 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 90 173
  (Polychromatic418967fa.accept_11_5_2_8_1_866 38 90 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 90 173 (accept_3_2 37 90 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  90 173 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 90 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 90 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 90 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 90 173 (accept_3_2 34 90 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 90 173 (Polychromatic418967fa.accept_13_7_12_4_1_450 33 90 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 90 173
  (Polychromatic418967fa.accept_7_4_6_5_1_141 32 90 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 90 173 (accept_3_2 31 90 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  90 173 (Polychromatic418967fa.accept_16_14_10_13_1_2768 30 90 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 90 173 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 90 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 90 173 (accept_3_2 28 90 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 90 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 90 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 90 173
  (Polychromatic418967fa.accept_19_7_14_2_1_4095 26 90 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 90 173 (accept_3_2 25 90 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  90 173 (Polychromatic418967fa.accept_13_11_12_4_1_3945 24 90 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 90 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 90 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 90 173 (accept_3_2 22 90 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 90 173 (Polychromatic418967fa.accept_13_8_12_4_1_4858 21 90 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 90 173
  (Polychromatic418967fa.accept_13_7_12_4_1_450 20 90 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 90 173 (accept_3_2 19 90 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  90 173 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 90 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 90 173 (Polychromatic418967fa.accept_19_17_14_2_1_4116 17 90 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 90 173 (accept_3_2 16 90 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 90 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 90 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 90 173
  (Polychromatic418967fa.accept_16_14_10_13_1_2768 14 90 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 90 173 (accept_3_2 13 90 173 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 90 173 (Polychromatic418967fa.accept_16_12_10_13_1_1042 12 90 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 90 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 90 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 90 173 (accept_3_2 10 90 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 90 173 (Polychromatic418967fa.accept_20_9_10_13_1_3835
  9 90 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 90 173
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 90 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 90 173 (accept_3_2 7 90 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 90
  173 (Polychromatic418967fa.accept_17_6_5_3_1_7134 6 90 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 90 173 (Polychromatic418967fa.accept_11_5_2_8_1_866 5 90 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 90 173 (accept_3_2 4 90 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 90 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 90 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 90 173
  (Polychromatic418967fa.accept_13_2_12_4_1_943 2 90 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 90 173 (accept_3_2 1 90 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  173)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 85 89 173 (Eq.refl
  Bool.true) (allA_succ_of_accept 84 89 173 (Polychromatic418967fa.accept_8_4_1_5_1_186 84 89 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 173 (Polychromatic418967fa.accept_19_7_13_2_1_2878
  83 89 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 89 173 (accept_3_2 82
  89 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 89 173
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 81 89 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 89 173 (Polychromatic418967fa.accept_13_2_11_4_1_445 80 89 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 173 (accept_3_2 79 89 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 89 173 (Polychromatic418967fa.accept_9_6_8_2_1_410 78 89 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 173 (Polychromatic418967fa.accept_9_5_8_2_1_409 77
  89 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 89 173 (accept_3_2 76 89
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 89 173
  (Polychromatic418967fa.accept_9_3_8_2_1_162 75 89 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 89 173 (Polychromatic418967fa.accept_10_4_9_3_1_1907 74 89 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 173 (accept_3_2 73 89 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 89 173 (Polychromatic418967fa.accept_13_7_11_4_1_2247 72 89 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 173
  (Polychromatic418967fa.accept_13_6_11_4_1_938 71 89 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 89 173 (accept_3_2 70 89 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  89 173 (Polychromatic418967fa.accept_9_6_8_2_1_410 69 89 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 89 173 (Polychromatic418967fa.accept_8_4_1_5_1_186 68 89 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 173 (accept_3_2 67 89 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 173 (Polychromatic418967fa.accept_9_3_8_2_1_162 66 89 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 173
  (Polychromatic418967fa.accept_15_5_14_8_1_1376 65 89 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 173 (accept_3_2 64 89 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 173 (Polychromatic418967fa.accept_19_6_13_2_1_8365 63 89 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 173 (Polychromatic418967fa.accept_13_10_11_4_1_2248 62 89 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 173 (accept_3_2 61 89 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 173 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 89 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 173
  (Polychromatic418967fa.accept_9_5_8_2_1_409 59 89 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 173 (accept_3_2 58 89 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 173 (Polychromatic418967fa.accept_9_3_8_2_1_162 57 89 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 173 (Polychromatic418967fa.accept_10_6_9_3_1_935 56 89 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 173 (accept_3_2 55 89 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 173 (Polychromatic418967fa.accept_10_4_9_3_1_1907 54 89 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 173
  (Polychromatic418967fa.accept_16_5_9_13_1_3845 53 89 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 173 (accept_3_2 52 89 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 173 (Polychromatic418967fa.accept_9_6_8_2_1_410 51 89 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 173 (Polychromatic418967fa.accept_9_5_8_2_1_409 50 89 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 173 (accept_3_2 49 89 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 173 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 89 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 173
  (Polychromatic418967fa.accept_13_8_11_4_1_1553 47 89 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 173 (accept_3_2 46 89 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 173 (Polychromatic418967fa.accept_13_6_11_4_1_938 45 89 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 173 (Polychromatic418967fa.accept_8_4_1_5_1_186 44 89 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 173 (accept_3_2 43 89 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 173 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 89 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 173
  (Polychromatic418967fa.accept_9_5_8_2_1_409 41 89 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 173 (accept_3_2 40 89 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 173 (Polychromatic418967fa.accept_9_3_8_2_1_162 39 89 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 173 (Polychromatic418967fa.accept_13_12_11_4_1_3111 38 89 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 173 (accept_3_2 37 89 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 173 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 89 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 173
  (Polychromatic418967fa.accept_15_5_14_8_1_1376 35 89 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 173 (accept_3_2 34 89 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 173 (Polychromatic418967fa.accept_9_6_8_2_1_410 33 89 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 173 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 89 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 173 (accept_3_2 31 89 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 173 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 89 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 173
  (Polychromatic418967fa.accept_19_10_13_2_1_9771 29 89 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 173 (accept_3_2 28 89 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 173 (Polychromatic418967fa.accept_19_8_13_2_1_6921 27 89 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 173 (Polychromatic418967fa.accept_10_6_9_3_1_935 26 89 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 173 (accept_3_2 25 89 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 173 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 89 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 173
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 89 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 173 (accept_3_2 22 89 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 173 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 89 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 173 (Polychromatic418967fa.accept_8_4_1_5_1_186 20 89 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 173 (accept_3_2 19 89 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 173 (Polychromatic418967fa.accept_22_18_1_19_1_6422 18 89 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 173
  (Polychromatic418967fa.accept_16_1_9_13_1_1822 17 89 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 173 (accept_3_2 16 89 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 173 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 89 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 173 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 89 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 173 (accept_3_2 13 89 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 173 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 89 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 173
  (Polychromatic418967fa.accept_19_11_13_2_1_9770 11 89 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 173 (accept_3_2 10 89 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 173 (Polychromatic418967fa.accept_15_9_14_8_1_1396 9 89 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 173 (Polychromatic418967fa.accept_13_8_11_4_1_1553 8 89 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 173 (accept_3_2 7 89 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 173 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 89 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 173
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 89 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 173 (accept_3_2 4 89 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  173 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 89 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 173 (Polychromatic418967fa.accept_13_2_11_4_1_445 2 89 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 173 (accept_3_2 1 89 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 173)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 86 88 173 (Eq.refl Bool.true) (allA_of_3_0 86 88 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ
  87 173 (allA_succ_of_accept 86 87 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 87 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 87 173 (accept_3_2 85 87 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 87 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 84 87 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 87 173 (Polychromatic418967fa.accept_13_5_9_4_1_441
  83 87 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 173 (accept_3_2 82
  87 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 173
  (Polychromatic418967fa.accept_12_9_3_5_1_423 81 87 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 87 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 87 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 87 173 (accept_3_2 79 87 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 87 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 87 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 87 173 (Polychromatic418967fa.accept_9_5_6_2_1_161 77
  87 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 173 (accept_3_2 76 87
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 173
  (Polychromatic418967fa.accept_9_3_6_2_1_160 75 87 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 87 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 87 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 87 173 (accept_3_2 73 87 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 87 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 72 87 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 87 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 71
  87 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 173 (accept_3_2 70 87
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 173
  (Polychromatic418967fa.accept_12_9_3_5_1_423 69 87 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 87 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 87 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 87 173 (accept_3_2 67 87 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 87 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 87 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 87 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 65
  87 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 173 (accept_3_2 64 87
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 173
  (Polychromatic418967fa.accept_15_3_12_8_1_738 63 87 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 87 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 87 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 87 173 (accept_3_2 61 87 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 87 173 (Polychromatic418967fa.accept_13_8_9_4_1_1552 60 87 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 87 173 (Polychromatic418967fa.accept_9_5_6_2_1_161 59
  87 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 173 (accept_3_2 58 87
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 173 (Polychromatic418967fa.accept_7_1_3_5_1_33
  57 87 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 87 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 87 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 87 173 (accept_3_2 55 87 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  87 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 87 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 87 173 (Polychromatic418967fa.accept_9_8_6_2_1_744 53 87 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 173 (accept_3_2 52 87 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 87 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 87 173
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 87 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 87 173 (accept_3_2 49 87 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  87 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 87 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 87 173 (Polychromatic418967fa.accept_13_8_9_4_1_1552 47 87 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 173 (accept_3_2 46 87 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 173 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 87 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 87 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 87 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 87 173 (accept_3_2 43 87 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  87 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 87 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 87 173 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 87 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 173 (accept_3_2 40 87 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 87 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 87 173
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 87 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 87 173 (accept_3_2 37 87 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  87 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 87 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 87 173 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 87 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 173 (accept_3_2 34 87 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 173 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 87 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 87 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 87 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 87 173 (accept_3_2 31 87 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  87 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 87 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 87 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 87 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 173 (accept_3_2 28 87 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 173 (Polychromatic418967fa.accept_18_9_15_11_1_5693 27 87 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 87 173
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 87 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 87 173 (accept_3_2 25 87 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  87 173 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 87 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 87 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 87 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 173 (accept_3_2 22 87 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 87 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 87 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 87 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 173 (accept_3_2 19 87 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  87 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 87 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 87 173 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 87 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 173 (accept_3_2 16 87 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 87 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 173
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 87 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 87 173 (accept_3_2 13 87 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  87 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 87 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 87 173 (Polychromatic418967fa.accept_15_11_12_8_1_739 11 87 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 173 (accept_3_2 10 87 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 87 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 87 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 173 (accept_3_2 7 87 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87
  173 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 87 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 87 173 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 87 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 173 (accept_3_2 4 87 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 87 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 87 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 87
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 173 (accept_3_2 1 87 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  173))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 173
  (allA_succ_of_accept 85 86 173 (accept_3_2 85 86 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  86 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 84 86 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 86 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 86 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 86 173 (accept_3_2 82 86 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 86 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 86 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 86 173
  (Polychromatic418967fa.accept_7_3_2_5_1_147 80 86 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 86 173 (accept_3_2 79 86 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  86 173 (Polychromatic418967fa.accept_9_6_5_2_1_421 78 86 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 86 173 (Polychromatic418967fa.accept_10_7_6_3_1_927 77 86 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 86 173 (accept_3_2 76 86 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 86 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 86 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 86 173
  (Polychromatic418967fa.accept_7_4_2_5_1_527 74 86 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 86 173 (accept_3_2 73 86 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  86 173 (Polychromatic418967fa.accept_15_12_11_8_1_1392 72 86 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 86 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 86 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 86 173 (accept_3_2 70 86 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 86 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 86 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 86 173
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 68 86 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 86 173 (accept_3_2 67 86 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  86 173 (Polychromatic418967fa.accept_7_3_2_5_1_147 66 86 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 86 173 (Polychromatic418967fa.accept_11_10_9_8_1_1974 65 86 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 86 173 (accept_3_2 64 86 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 86 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 86 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 86 173
  (Polychromatic418967fa.accept_9_8_5_2_1_422 62 86 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 86 173 (accept_3_2 61 86 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  86 173 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 86 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 86 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 86 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 86 173 (accept_3_2 58 86 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 86 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 86 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 86 173
  (Polychromatic418967fa.accept_12_8_2_5_1_844 56 86 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 86 173 (accept_3_2 55 86 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  86 173 (Polychromatic418967fa.accept_11_10_9_8_1_1974 54 86 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 86 173 (Polychromatic418967fa.accept_7_4_2_5_1_527 53 86 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 86 173 (accept_3_2 52 86 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 86 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 86 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 86 173
  (Polychromatic418967fa.accept_13_11_8_4_1_3950 50 86 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 86 173 (accept_3_2 49 86 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  86 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 86 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 86 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 86 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 86 173 (accept_3_2 46 86 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 86 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 86 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 86 173
  (Polychromatic418967fa.accept_9_8_5_2_1_422 44 86 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 86 173 (accept_3_2 43 86 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  86 173 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 86 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 86 173 (Polychromatic418967fa.accept_16_9_6_13_1_3831 41 86 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 86 173 (accept_3_2 40 86 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 86 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 86 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 86 173
  (Polychromatic418967fa.accept_7_3_2_5_1_147 38 86 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 86 173 (accept_3_2 37 86 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  86 173 (Polychromatic418967fa.accept_13_10_8_4_1_3098 36 86 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 86 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 86 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 86 173 (accept_3_2 34 86 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 86 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 86 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 86 173
  (Polychromatic418967fa.accept_7_4_2_5_1_527 32 86 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 86 173 (accept_3_2 31 86 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  86 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 86 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 86 173 (Polychromatic418967fa.accept_10_9_6_3_1_545 29 86 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 86 173 (accept_3_2 28 86 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 86 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 86 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 86 173
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 86 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 86 173 (accept_3_2 25 86 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  86 173 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 86 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 86 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 86 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 86 173 (accept_3_2 22 86 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 86 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 86 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 86 173
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 86 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 86 173 (accept_3_2 19 86 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  86 173 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 86 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 86 173 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 86 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 86 173 (accept_3_2 16 86 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 86 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 86 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 86 173
  (Polychromatic418967fa.accept_26_14_8_17_1_9769 14 86 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 86 173 (accept_3_2 13 86 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  86 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 86 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 86 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 86 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 86 173 (accept_3_2 10 86 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 86 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 86 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 173
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 86 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 86 173 (accept_3_2 7 86 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86
  173 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 86 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 86 173 (Polychromatic418967fa.accept_15_5_11_8_1_1391 5 86 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 86 173 (accept_3_2 4 86 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 86 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 86 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 86 173 (Polychromatic418967fa.accept_17_2_1_3_1_2357 2
  86 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 86 173 (accept_3_2 1 86 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  173)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 173
  (allA_of_3_0 85 85 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 84 173 (allA_succ_of_accept 83 84 173
  (Polychromatic418967fa.accept_13_5_6_4_1_1582 83 84 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 84 173 (accept_3_2 82 84 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  84 173 (Polychromatic418967fa.accept_8_1_4_5_1_48 81 84 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 84 173 (Polychromatic418967fa.accept_9_8_3_2_1_417 80 84 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 84 173 (accept_3_2 79 84 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 84 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 78 84 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 84 173
  (Polychromatic418967fa.accept_9_5_3_2_1_171 77 84 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 84 173 (accept_3_2 76 84 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  84 173 (Polychromatic418967fa.accept_13_10_6_4_1_1583 75 84 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 84 173 (Polychromatic418967fa.accept_13_9_6_4_1_2243 74 84 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 84 173 (accept_3_2 73 84 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 84 173 (Polychromatic418967fa.accept_13_7_6_4_1_933 72 84 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 84 173
  (Polychromatic418967fa.accept_9_8_3_2_1_417 71 84 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 84 173 (accept_3_2 70 84 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  84 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 69 84 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 84 173 (Polychromatic418967fa.accept_9_5_3_2_1_171 68 84 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 84 173 (accept_3_2 67 84 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 84 173 (Polychromatic418967fa.accept_23_20_15_12_1_6321 66 84 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 84 173
  (Polychromatic418967fa.accept_8_1_4_5_1_48 65 84 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 84 173 (accept_3_2 64 84 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  84 173 (Polychromatic418967fa.accept_13_11_6_4_1_3121 63 84 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 84 173 (Polychromatic418967fa.accept_9_8_3_2_1_417 62 84 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 84 173 (accept_3_2 61 84 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 84 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 84 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 84 173
  (Polychromatic418967fa.accept_9_5_3_2_1_171 59 84 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 84 173 (accept_3_2 58 84 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  84 173 (Polychromatic418967fa.accept_8_1_4_5_1_48 57 84 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 84 173 (Polychromatic418967fa.accept_16_8_4_13_1_1014 56 84 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 84 173 (accept_3_2 55 84 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 84 173 (Polychromatic418967fa.accept_13_2_6_4_1_1593 54 84 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 84 173
  (Polychromatic418967fa.accept_9_8_3_2_1_417 53 84 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 84 173 (accept_3_2 52 84 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  84 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 84 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 84 173 (Polychromatic418967fa.accept_9_5_3_2_1_171 50 84 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 84 173 (accept_3_2 49 84 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 84 173 (Polychromatic418967fa.accept_11_4_7_8_1_1926 48 84 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 84 173
  (Polychromatic418967fa.accept_10_7_4_3_1_560 47 84 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 84 173 (accept_3_2 46 84 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  84 173 (Polychromatic418967fa.accept_18_9_12_11_1_5642 45 84 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 84 173 (Polychromatic418967fa.accept_9_8_3_2_1_417 44 84 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 84 173 (accept_3_2 43 84 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 84 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 84 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 84 173
  (Polychromatic418967fa.accept_8_1_4_5_1_48 41 84 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 84 173 (accept_3_2 40 84 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  84 173 (Polychromatic418967fa.accept_10_9_4_3_1_539 39 84 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 84 173 (Polychromatic418967fa.accept_16_6_4_13_1_3841 38 84 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 84 173 (accept_3_2 37 84 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 84 173 (Polychromatic418967fa.accept_13_10_6_4_1_1583 36 84
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 84 173
  (Polychromatic418967fa.accept_9_8_3_2_1_417 35 84 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 84 173 (accept_3_2 34 84 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  84 173 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 84 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 84 173 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 84 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 84 173 (accept_3_2 31 84 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 84 173 (Polychromatic418967fa.accept_17_13_16_3_1_1431 30 84 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 84 173
  (Polychromatic418967fa.accept_10_9_4_3_1_539 29 84 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 84 173 (accept_3_2 28 84 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  84 173 (Polychromatic418967fa.accept_10_7_4_3_1_560 27 84 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 84 173 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 84 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 84 173 (accept_3_2 25 84 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 84 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 84 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 84 173
  (Polychromatic418967fa.accept_9_5_3_2_1_171 23 84 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 84 173 (accept_3_2 22 84 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  84 173 (Polychromatic418967fa.accept_17_4_16_3_1_4620 21 84 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 84 173 (Polychromatic418967fa.accept_13_7_6_4_1_933 20 84 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 173 (accept_3_2 19 84 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 84 173 (Polychromatic418967fa.accept_13_5_6_4_1_1582 18 84 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 84 173
  (Polychromatic418967fa.accept_8_1_4_5_1_48 17 84 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 84 173 (accept_3_2 16 84 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  84 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 84 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 84 173 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 84 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 173 (accept_3_2 13 84 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 84 173 (Polychromatic418967fa.accept_16_12_4_13_1_3827 12 84 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 84 173
  (Polychromatic418967fa.accept_13_11_6_4_1_3121 11 84 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 84 173 (accept_3_2 10 84 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  84 173 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 84 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 84 173 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 84 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 173 (accept_3_2 7 84 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 84 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 84 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 84 173
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 84 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 84 173 (accept_3_2 4 84 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 84
  173 (Polychromatic418967fa.accept_15_3_9_8_1_3164 3 84 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 84 173 (Polychromatic418967fa.accept_13_2_6_4_1_1593 2 84 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 173 (accept_3_2 1 84 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 84
  173)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 173
  (allA_succ_of_accept 82 83 173 (accept_3_2 82 83 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  83 173 (Polychromatic418967fa.accept_7_4_6_5_1_141 81 83 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 83 173 (Polychromatic418967fa.accept_11_3_6_8_1_1924 80 83 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 173 (accept_3_2 79 83 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 83 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 173
  (Polychromatic418967fa.accept_13_12_5_4_1_3133 77 83 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 173 (accept_3_2 76 83 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 173 (Polychromatic418967fa.accept_13_10_5_4_1_3107 75 83 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 83 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 173 (accept_3_2 73 83 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 173 (Polychromatic418967fa.accept_16_8_3_13_1_7295 72 83 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 173
  (Polychromatic418967fa.accept_7_1_6_5_1_39 71 83 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 173 (accept_3_2 70 83 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 173 (Polychromatic418967fa.accept_11_3_6_8_1_1924 69 83 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 173 (Polychromatic418967fa.accept_20_8_3_13_1_2590 68 83 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 173 (accept_3_2 67 83 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 83 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 173
  (Polychromatic418967fa.accept_16_1_3_13_1_2785 65 83 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 173 (accept_3_2 64 83 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 173 (Polychromatic418967fa.accept_16_15_3_13_1_2818 63 83 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 83 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 173 (accept_3_2 61 83 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 173 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 83 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 173
  (Polychromatic418967fa.accept_25_9_8_23_1_7913 59 83 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 173 (accept_3_2 58 83 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 173 (Polychromatic418967fa.accept_7_1_6_5_1_39 57 83 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 173 (Polychromatic418967fa.accept_16_8_3_13_1_7295 56 83 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 173 (accept_3_2 55 83 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 83 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 173
  (Polychromatic418967fa.accept_7_4_6_5_1_141 53 83 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 173 (accept_3_2 52 83 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 173 (Polychromatic418967fa.accept_13_12_5_4_1_3133 51 83 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 83 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 173 (accept_3_2 49 83 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 173 (Polychromatic418967fa.accept_13_9_5_4_1_1591 48 83 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 173
  (Polychromatic418967fa.accept_11_3_6_8_1_1924 47 83 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 173 (accept_3_2 46 83 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 173 (Polychromatic418967fa.accept_13_6_5_4_1_3924 45 83 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 173 (Polychromatic418967fa.accept_20_4_3_13_1_8257 44 83 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 173 (accept_3_2 43 83 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 83 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 173
  (Polychromatic418967fa.accept_13_2_5_4_1_3926 41 83 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 173 (accept_3_2 40 83 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 173 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 83 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 83 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 173 (accept_3_2 37 83 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 173 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 83 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 173
  (Polychromatic418967fa.accept_13_9_5_4_1_1591 35 83 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 173 (accept_3_2 34 83 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 173 (Polychromatic418967fa.accept_16_1_3_13_1_2785 33 83 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 173 (Polychromatic418967fa.accept_7_4_6_5_1_141 32 83 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 173 (accept_3_2 31 83 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 83 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 173
  (Polychromatic418967fa.accept_7_1_6_5_1_39 29 83 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 173 (accept_3_2 28 83 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 173 (Polychromatic418967fa.accept_13_1_5_4_1_463 27 83 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 83 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 173 (accept_3_2 25 83 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 173 (Polychromatic418967fa.accept_16_8_3_13_1_7295 24 83 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 173
  (Polychromatic418967fa.accept_13_10_5_4_1_3107 23 83 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 173 (accept_3_2 22 83 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 173 (Polychromatic418967fa.accept_20_1_3_13_1_8217 21 83 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 173 (Polychromatic418967fa.accept_14_6_13_5_1_534 20 83 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 173 (accept_3_2 19 83 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 83 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 173
  (Polychromatic418967fa.accept_16_1_3_13_1_2785 17 83 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 173 (accept_3_2 16 83 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 173 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 83 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 83 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 173 (accept_3_2 13 83 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 173 (Polychromatic418967fa.accept_13_12_5_4_1_3133 12 83 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 173
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 83 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 173 (accept_3_2 10 83 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 173 (Polychromatic418967fa.accept_13_9_5_4_1_1591 9 83 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 173 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 83 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 173 (accept_3_2 7 83 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 83 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 173
  (Polychromatic418967fa.accept_19_5_7_2_1_1728 5 83 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 173 (accept_3_2 4 83 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  173 (Polychromatic418967fa.accept_11_3_6_8_1_1924 3 83 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 83 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 83 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 173 (accept_3_2 1 83 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 83
  173))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 82 173 (allA_of_3_0
  82 82 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 81 173 (allA_succ_of_accept 80 81 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 81 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 81 173 (accept_3_2 79 81 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  81 173 (Polychromatic418967fa.accept_7_1_4_5_1_35 78 81 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 81 173 (Polychromatic418967fa.accept_13_12_3_4_1_928 77 81 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 173 (accept_3_2 76 81 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 173 (Polychromatic418967fa.accept_12_3_9_5_1_853 75 81 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 81 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 74 81 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 81 173 (accept_3_2 73 81 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  81 173 (Polychromatic418967fa.accept_7_2_4_5_1_313 72 81 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 81 173 (Polychromatic418967fa.accept_7_1_4_5_1_35 71 81 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 173 (accept_3_2 70 81 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 173 (Polychromatic418967fa.accept_7_6_4_5_1_314 69 81 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 81 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 81 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 81 173 (accept_3_2 67 81 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  81 173 (Polychromatic418967fa.accept_13_1_3_4_1_925 66 81 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 81 173 (Polychromatic418967fa.accept_7_2_4_5_1_313 65 81 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 173 (accept_3_2 64 81 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 173 (Polychromatic418967fa.accept_12_3_9_5_1_853 63 81 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 81 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 81 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 81 173 (accept_3_2 61 81 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  81 173 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 81 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 81 173 (Polychromatic418967fa.accept_13_7_3_4_1_459 59 81 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 173 (accept_3_2 58 81 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 173 (Polychromatic418967fa.accept_7_1_4_5_1_35 57 81 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 81 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 81 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 81 173 (accept_3_2 55 81 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  81 173 (Polychromatic418967fa.accept_19_16_5_2_1_8375 54 81 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 81 173 (Polychromatic418967fa.accept_13_1_3_4_1_925 53 81 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 173 (accept_3_2 52 81 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 173 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 81 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 81 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 81 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 81 173 (accept_3_2 49 81 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  81 173 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 81 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 81 173 (Polychromatic418967fa.accept_15_2_6_8_1_754 47 81 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 173 (accept_3_2 46 81 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 173 (Polychromatic418967fa.accept_11_1_4_8_1_1918 45 81 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 81 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 81 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 81 173 (accept_3_2 43 81 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  81 173 (Polychromatic418967fa.accept_10_2_1_3_1_233 42 81 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 81 173 (Polychromatic418967fa.accept_7_6_4_5_1_314 41 81 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 173 (accept_3_2 40 81 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 173 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 81 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 81 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 81 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 81 173 (accept_3_2 37 81 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  81 173 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 81 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 81 173 (Polychromatic418967fa.accept_16_3_1_13_1_4968 35 81 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 173 (accept_3_2 34 81 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 173 (Polychromatic418967fa.accept_13_7_3_4_1_459 33 81 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 81 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 81 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 81 173 (accept_3_2 31 81 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  81 173 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 81 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 81 173 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 81 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 173 (accept_3_2 28 81 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 173 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 81 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 81 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 81 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 81 173 (accept_3_2 25 81 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  81 173 (Polychromatic418967fa.accept_21_3_18_5_1_8211 24 81 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 81 173 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 81 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 173 (accept_3_2 22 81 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 173 (Polychromatic418967fa.accept_16_5_1_13_1_1053 21 81 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 81 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 81 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 81 173 (accept_3_2 19 81 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  81 173 (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 81 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 81 173 (Polychromatic418967fa.accept_15_2_6_8_1_754 17 81 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 173 (accept_3_2 16 81 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 173 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 81 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 81 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 81 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 81 173 (accept_3_2 13 81 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  81 173 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 81 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 81 173 (Polychromatic418967fa.accept_21_11_18_5_1_8162 11 81 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 173 (accept_3_2 10 81 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 173 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 81 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 81 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 81 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 81 173 (accept_3_2 7 81 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 81
  173 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 81 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 81 173 (Polychromatic418967fa.accept_16_5_1_13_1_1053 5 81 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 173 (accept_3_2 4 81 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 81 173 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 81 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 81
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 173 (accept_3_2 1 81 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81
  173))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 173
  (allA_succ_of_accept 79 80 173 (accept_3_2 79 80 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  80 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 78 80 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 80 173 (Polychromatic418967fa.accept_9_5_8_2_1_409 77 80 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 80 173 (accept_3_2 76 80 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 80 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 80 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 80 173
  (Polychromatic418967fa.accept_12_2_8_5_1_408 74 80 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 80 173 (accept_3_2 73 80 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  80 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 72 80 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 80 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 71 80 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 80 173 (accept_3_2 70 80 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 80 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 80 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 80 173
  (Polychromatic418967fa.accept_9_5_8_2_1_409 68 80 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 80 173 (accept_3_2 67 80 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  80 173 (Polychromatic418967fa.accept_9_3_8_2_1_162 66 80 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 80 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 65 80 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 80 173 (accept_3_2 64 80 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 80 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 80 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 80 173
  (Polychromatic418967fa.accept_12_2_8_5_1_408 62 80 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 80 173 (accept_3_2 61 80 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  80 173 (Polychromatic418967fa.accept_9_6_8_2_1_410 60 80 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 80 173 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 80 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 80 173 (accept_3_2 58 80 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 80 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 80 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 80 173
  (Polychromatic418967fa.accept_15_11_5_8_1_3157 56 80 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 80 173 (accept_3_2 55 80 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  80 173 (Polychromatic418967fa.accept_14_12_10_5_1_2712 54 80 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 80 173 (Polychromatic418967fa.accept_21_11_17_5_1_8161 53 80 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 80 173 (accept_3_2 52 80 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 80 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 80 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 80 173
  (Polychromatic418967fa.accept_7_1_3_5_1_33 50 80 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 80 173 (accept_3_2 49 80 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  80 173 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 80 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 80 173 (Polychromatic418967fa.accept_19_9_4_2_1_9753 47 80 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 80 173 (accept_3_2 46 80 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 80 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 80 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 80 173
  (Polychromatic418967fa.accept_7_2_3_5_1_34 44 80 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 80 173 (accept_3_2 43 80 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  80 173 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 80 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 80 173 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 80 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 80 173 (accept_3_2 40 80 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 80 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 80 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 80 173
  (Polychromatic418967fa.accept_11_5_3_8_1_454 38 80 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 80 173 (accept_3_2 37 80 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  80 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 80 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 80 173 (Polychromatic418967fa.accept_19_16_4_2_1_4102 35 80 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 80 173 (accept_3_2 34 80 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 80 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 80 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 80 173
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 80 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 80 173 (accept_3_2 31 80 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  80 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 80 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 80 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 80 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 80 173 (accept_3_2 28 80 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 80 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 80 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 80 173
  (Polychromatic418967fa.accept_12_2_8_5_1_408 26 80 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 80 173 (accept_3_2 25 80 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  80 173 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 80 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 80 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 80 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 80 173 (accept_3_2 22 80 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 80 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 80 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 80 173
  (Polychromatic418967fa.accept_23_20_11_12_1_9768 20 80 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 80 173 (accept_3_2 19 80 173 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 80 173 (Polychromatic418967fa.accept_13_5_2_4_1_3955 18 80 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 80 173 (Polychromatic418967fa.accept_11_6_3_8_1_843 17 80 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 80 173 (accept_3_2 16 80 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 80 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 15
  80 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 80 173
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 80 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 80 173 (accept_3_2 13 80 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  80 173 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 80 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 80 173 (Polychromatic418967fa.accept_13_11_2_4_1_1590 11 80 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 80 173 (accept_3_2 10 80 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 80 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 80 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 80 173
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 80 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 80 173 (accept_3_2 7 80 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 80
  173 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 80 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 80 173 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 80 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 80 173 (accept_3_2 4 80 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 80 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 80 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 80 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 80
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 80 173 (accept_3_2 1 80 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  173)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 79 173 (allA_of_3_0 79
  79 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 78 173 (allA_succ_of_accept 77 78 173
  (Polychromatic418967fa.accept_9_5_6_2_1_161 77 78 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 78 173 (accept_3_2 76 78 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  78 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 78 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 78 173 (Polychromatic418967fa.accept_7_4_1_5_1_540 74 78 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 78 173 (accept_3_2 73 78 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 78 173 (Polychromatic418967fa.accept_15_12_3_8_1_5245 72 78 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 78 173
  (Polychromatic418967fa.accept_4_3_2_1_1_50 71 78 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 78 173 (accept_3_2 70 78 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  78 173 (Polychromatic418967fa.accept_7_6_1_5_1_322 69 78 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 78 173 (Polychromatic418967fa.accept_9_5_6_2_1_161 68 78 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 173 (accept_3_2 67 78 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 78 173 (Polychromatic418967fa.accept_7_3_1_5_1_44 66 78 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 78 173
  (Polychromatic418967fa.accept_10_5_8_3_1_229 65 78 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 78 173 (accept_3_2 64 78 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  78 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 78 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 78 173 (Polychromatic418967fa.accept_7_6_1_5_1_322 62 78 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 173 (accept_3_2 61 78 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 78 173 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 78 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 78 173
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 78 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 78 173 (accept_3_2 58 78 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  78 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 78 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 78 173 (Polychromatic418967fa.accept_10_6_8_3_1_930 56 78 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 78 173 (accept_3_2 55 78 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 78 173 (Polychromatic418967fa.accept_15_9_3_8_1_3155 54 78 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 78 173
  (Polychromatic418967fa.accept_7_4_1_5_1_540 53 78 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 78 173 (accept_3_2 52 78 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  78 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 78 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 78 173 (Polychromatic418967fa.accept_9_5_6_2_1_161 50 78 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 173 (accept_3_2 49 78 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 78 173 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 78 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 78 173
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 78 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 78 173 (accept_3_2 46 78 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  78 173 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 78 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 78 173 (Polychromatic418967fa.accept_9_8_6_2_1_744 44 78 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 173 (accept_3_2 43 78 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 78 173 (Polychromatic418967fa.accept_15_12_3_8_1_5245 42 78 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 78 173
  (Polychromatic418967fa.accept_7_6_1_5_1_322 41 78 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 78 173 (accept_3_2 40 78 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  78 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 78 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 78 173 (Polychromatic418967fa.accept_7_3_1_5_1_44 38 78 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 78 173 (accept_3_2 37 78 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 78 173 (Polychromatic418967fa.accept_10_6_8_3_1_930 36 78 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 78 173
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 78 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 78 173 (accept_3_2 34 78 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  78 173 (Polychromatic418967fa.accept_16_1_14_13_1_3834 33 78 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 78 173 (Polychromatic418967fa.accept_7_4_1_5_1_540 32 78 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 173 (accept_3_2 31 78 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 78 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 78 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 78 173
  (Polychromatic418967fa.accept_21_8_15_5_1_8178 29 78 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 78 173 (accept_3_2 28 78 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  78 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 78 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 78 173 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 78 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 173 (accept_3_2 25 78 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 78 173 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 78 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 78 173
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 78 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 78 173 (accept_3_2 22 78 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  78 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 78 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 78 173 (Polychromatic418967fa.accept_7_6_1_5_1_322 20 78 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 173 (accept_3_2 19 78 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 173 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 78 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 78 173
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 78 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 78 173 (accept_3_2 16 78 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  78 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 78 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 78 173 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 78 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 173 (accept_3_2 13 78 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 78 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 78 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 78 173
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 78 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 78 173 (accept_3_2 10 78 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  78 173 (Polychromatic418967fa.accept_15_9_3_8_1_3155 9 78 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 78 173 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 78 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 173 (accept_3_2 7 78 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 78 173 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 78 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 78 173
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 78 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 78 173 (accept_3_2 4 78 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 78
  173 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 78 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 78 173 (Polychromatic418967fa.accept_20_2_18_13_1_3843 2 78 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 78 173 (accept_3_2 1 78 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 78 173)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  77 173 (allA_succ_of_accept 76 77 173 (accept_3_2 76 77 173 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 77 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 75 77 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 77 173 (Polychromatic418967fa.accept_10_4_7_3_1_54 74 77 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 173 (accept_3_2 73 77 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 173 (Polychromatic418967fa.accept_13_7_12_4_1_450
  72 77 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 173
  (Polychromatic418967fa.accept_9_8_5_2_1_422 71 77 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 77 173 (accept_3_2 70 77 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  77 173 (Polychromatic418967fa.accept_9_6_5_2_1_421 69 77 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 77 173 (Polychromatic418967fa.accept_13_3_12_4_1_110 68 77 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 173 (accept_3_2 67 77 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 66 77 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 173
  (Polychromatic418967fa.accept_10_5_7_3_1_561 65 77 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 173 (accept_3_2 64 77 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  77 173 (Polychromatic418967fa.accept_13_11_12_4_1_3945 63 77 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 77 173 (Polychromatic418967fa.accept_9_8_5_2_1_422 62 77 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 173 (accept_3_2 61 77 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 173 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 77 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 173
  (Polychromatic418967fa.accept_13_7_12_4_1_450 59 77 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 77 173 (accept_3_2 58 77 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 57 77 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 173 (Polychromatic418967fa.accept_10_6_7_3_1_547 56 77 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 173 (accept_3_2 55 77 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 173 (Polychromatic418967fa.accept_10_4_7_3_1_54 54 77 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 173
  (Polychromatic418967fa.accept_9_8_5_2_1_422 53 77 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 173 (accept_3_2 52 77 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 173 (Polychromatic418967fa.accept_9_6_5_2_1_421 51 77 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 173 (Polychromatic418967fa.accept_13_11_12_4_1_3945 50 77 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 173 (accept_3_2 49 77 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 77 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 173
  (Polychromatic418967fa.accept_13_8_12_4_1_4858 47 77 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 173 (accept_3_2 46 77 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 173 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 77 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 173 (Polychromatic418967fa.accept_9_8_5_2_1_422 44 77 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 173 (accept_3_2 43 77 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 173 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 77 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 173
  (Polychromatic418967fa.accept_13_2_12_4_1_943 41 77 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 173 (accept_3_2 40 77 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 77 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 173 (Polychromatic418967fa.accept_21_17_14_5_1_9767 38 77 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 173 (accept_3_2 37 77 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 173 (Polychromatic418967fa.accept_10_6_7_3_1_547 36 77 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 173
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 77 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 173 (accept_3_2 34 77 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 173 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 77 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 173 (Polychromatic418967fa.accept_18_14_5_11_1_5676 32 77 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 173 (accept_3_2 31 77 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 77 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 173
  (Polychromatic418967fa.accept_13_3_12_4_1_110 29 77 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 173 (accept_3_2 28 77 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 173 (Polychromatic418967fa.accept_17_10_9_3_1_7144 27 77 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 173 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 77 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 173 (accept_3_2 25 77 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 173 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 77 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 173
  (Polychromatic418967fa.accept_14_9_7_5_1_1105 23 77 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 173 (accept_3_2 22 77 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 77 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 173 (Polychromatic418967fa.accept_13_7_12_4_1_450 20 77 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 173 (accept_3_2 19 77 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 173 (Polychromatic418967fa.accept_13_5_12_4_1_449 18 77 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 173
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 77 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 173 (accept_3_2 16 77 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 173 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 77 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 173 (Polychromatic418967fa.accept_10_4_7_3_1_54 14 77 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 173 (accept_3_2 13 77 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 77 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 173
  (Polychromatic418967fa.accept_13_11_12_4_1_3945 11 77 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 173 (accept_3_2 10 77 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 173 (Polychromatic418967fa.accept_14_9_7_5_1_1105 9 77 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 173 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 77 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 173 (accept_3_2 7 77 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 173 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 77 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 173
  (Polychromatic418967fa.accept_10_5_7_3_1_561 5 77 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 173 (accept_3_2 4 77 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  173 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 77 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 173 (Polychromatic418967fa.accept_13_2_12_4_1_943 2 77 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 173 (accept_3_2 1 77 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 173))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  76 173 (allA_of_3_0 76 76 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 75 173 (allA_succ_of_accept 74 75
  173 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 75 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 75 173 (accept_3_2 73 75 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  75 173 (Polychromatic418967fa.accept_10_2_5_3_1_1408 72 75 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 75 173 (Polychromatic418967fa.accept_9_8_3_2_1_417 71 75 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 75 173 (accept_3_2 70 75 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 69 75 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 75 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 75 173 (accept_3_2 67 75 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  75 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 75 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 75 173 (Polychromatic418967fa.accept_11_10_9_8_1_1974 65 75 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 173 (accept_3_2 64 75 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 173 (Polychromatic418967fa.accept_13_11_10_4_1_1565 63 75
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 173
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 75 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 173 (accept_3_2 61 75 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  75 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 75 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 75 173 (Polychromatic418967fa.accept_9_5_3_2_1_171 59 75 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 173 (accept_3_2 58 75 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 173 (Polychromatic418967fa.accept_10_7_5_3_1_542 57 75 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 75 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 75 173 (accept_3_2 55 75 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  75 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 75 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 75 173 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 75 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 173 (accept_3_2 52 75 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 75 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 173
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 75 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 75 173 (accept_3_2 49 75 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  75 173 (Polychromatic418967fa.accept_10_8_5_3_1_543 48 75 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 75 173 (Polychromatic418967fa.accept_10_7_5_3_1_542 47 75 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 173 (accept_3_2 46 75 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 173 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 75 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 75 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 75 173 (accept_3_2 43 75 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  75 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 75 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 75 173 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 75 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 173 (accept_3_2 40 75 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 173 (Polychromatic418967fa.accept_19_1_18_2_1_2835 39 75 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 173
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 75 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 75 173 (accept_3_2 37 75 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  75 173 (Polychromatic418967fa.accept_21_15_12_5_1_9766 36 75 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 75 173 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 75 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 173 (accept_3_2 34 75 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 75 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 75 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 173 (accept_3_2 31 75 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  75 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 75 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 75 173 (Polychromatic418967fa.accept_17_12_7_3_1_1498 29 75 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 173 (accept_3_2 28 75 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 173 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 75 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 173
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 75 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 75 173 (accept_3_2 25 75 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  75 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 75 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 75 173 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 75 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 173 (accept_3_2 22 75 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 173 (Polychromatic418967fa.accept_11_10_9_8_1_1974 21 75 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 75 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 75 173 (accept_3_2 19 75 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  75 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 75 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 75 173 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 75 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 173 (accept_3_2 16 75 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 75 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 173
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 75 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 173 (accept_3_2 13 75 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  75 173 (Polychromatic418967fa.accept_10_2_5_3_1_1408 12 75 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 75 173 (Polychromatic418967fa.accept_13_11_10_4_1_1565 11 75 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 173 (accept_3_2 10 75 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 173 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 75 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 75 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 173 (accept_3_2 7 75 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75
  173 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 75 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 173 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 75 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 173 (accept_3_2 4 75 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 75 173 (Polychromatic418967fa.accept_19_3_18_2_1_6935 3 75 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 75
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 173 (accept_3_2 1 75 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  173))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 173 (allA_succ_of_accept
  73 74 173 (accept_3_2 73 74 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 74 173
  (Polychromatic418967fa.accept_7_2_4_5_1_313 72 74 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 74 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 74 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 74 173 (accept_3_2 70 74 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 74 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 74 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 74 173 (Polychromatic418967fa.accept_12_8_2_5_1_844
  68 74 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 74 173 (accept_3_2 67
  74 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 74 173
  (Polychromatic418967fa.accept_15_6_14_8_1_245 66 74 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 74 173 (Polychromatic418967fa.accept_7_2_4_5_1_313 65 74 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 74 173 (accept_3_2 64 74 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 74 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 74 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 74 173 (Polychromatic418967fa.accept_7_6_4_5_1_314 62
  74 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 74 173 (accept_3_2 61 74
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 74 173
  (Polychromatic418967fa.accept_13_8_9_4_1_1552 60 74 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 74 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 74 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 74 173 (accept_3_2 58 74 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 74 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 74 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 74 173 (Polychromatic418967fa.accept_12_8_2_5_1_844
  56 74 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 74 173 (accept_3_2 55
  74 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 74 173
  (Polychromatic418967fa.accept_15_9_14_8_1_1396 54 74 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 74 173 (Polychromatic418967fa.accept_16_5_10_13_1_6042 53 74 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 74 173 (accept_3_2 52 74 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 74 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 74 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 74 173 (Polychromatic418967fa.accept_7_1_4_5_1_35 50
  74 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 74 173 (accept_3_2 49 74
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 74 173
  (Polychromatic418967fa.accept_7_6_4_5_1_314 48 74 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 74 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 74 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 74 173 (accept_3_2 46 74 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 74 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 74 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 74 173 (Polychromatic418967fa.accept_7_2_4_5_1_313 44
  74 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 74 173 (accept_3_2 43 74
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 74 173
  (Polychromatic418967fa.accept_19_4_17_2_1_5409 42 74 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 74 173 (Polychromatic418967fa.accept_7_6_4_5_1_314 41 74 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 74 173 (accept_3_2 40 74 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 74 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 74 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 74 173
  (Polychromatic418967fa.accept_21_17_11_5_1_5060 38 74 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 74 173 (accept_3_2 37 74 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  74 173 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 74 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 74 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 74 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 74 173 (accept_3_2 34 74 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 74 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 74 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 74 173
  (Polychromatic418967fa.accept_12_8_2_5_1_844 32 74 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 74 173 (accept_3_2 31 74 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  74 173 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 74 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 74 173 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 74 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 74 173 (accept_3_2 28 74 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 74 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 74 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 74 173
  (Polychromatic418967fa.accept_17_9_6_3_1_2398 26 74 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 74 173 (accept_3_2 25 74 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  74 173 (Polychromatic418967fa.accept_15_9_14_8_1_1396 24 74 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 74 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 74 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 74 173 (accept_3_2 22 74 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 74 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 74 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 74 173
  (Polychromatic418967fa.accept_7_6_4_5_1_314 20 74 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 74 173 (accept_3_2 19 74 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  74 173 (Polychromatic418967fa.accept_13_5_9_4_1_441 18 74 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 74 173 (Polychromatic418967fa.accept_10_7_4_3_1_560 17 74 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 74 173 (accept_3_2 16 74 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 74 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 74 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 74 173
  (Polychromatic418967fa.accept_16_14_10_13_1_2768 14 74 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 74 173 (accept_3_2 13 74 173 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 74 173 (Polychromatic418967fa.accept_16_12_10_13_1_1042 12 74 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 74 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 74 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 74 173 (accept_3_2 10 74 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 74 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 74
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 74 173
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 74 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 74 173 (accept_3_2 7 74 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 74
  173 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 74 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 74 173 (Polychromatic418967fa.accept_13_5_9_4_1_441 5 74 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 74 173 (accept_3_2 4 74 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 74 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 74 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 74 173 (Polychromatic418967fa.accept_7_2_4_5_1_313 2
  74 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 173 (accept_3_2 1 74 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  173)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73 173 (allA_of_3_0 73 73 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 72 173 (allA_succ_of_accept 71 72 173
  (Polychromatic418967fa.accept_10_1_2_3_1_1910 71 72 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 72 173 (accept_3_2 70 72 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  72 173 (Polychromatic418967fa.accept_11_3_6_8_1_1924 69 72 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 72 173 (Polychromatic418967fa.accept_13_3_7_4_1_435 68 72 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 72 173 (accept_3_2 67 72 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 72 173 (Polychromatic418967fa.accept_7_3_2_5_1_147 66 72 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 72 173
  (Polychromatic418967fa.accept_10_5_2_3_1_239 65 72 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 72 173 (accept_3_2 64 72 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  72 173 (Polychromatic418967fa.accept_13_11_7_4_1_1561 63 72 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 72 173 (Polychromatic418967fa.accept_13_10_7_4_1_2262 62 72 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 173 (accept_3_2 61 72 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 72 173 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 72 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 72 173
  (Polychromatic418967fa.accept_7_3_2_5_1_147 59 72 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 72 173 (accept_3_2 58 72 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  72 173 (Polychromatic418967fa.accept_21_15_9_5_1_6588 57 72 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 72 173 (Polychromatic418967fa.accept_15_11_12_8_1_739 56 72 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 173 (accept_3_2 55 72 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 72 173 (Polychromatic418967fa.accept_21_12_9_5_1_6547 54 72
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 72 173
  (Polychromatic418967fa.accept_7_4_2_5_1_527 53 72 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 72 173 (accept_3_2 52 72 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  72 173 (Polychromatic418967fa.accept_10_1_2_3_1_1910 51 72 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 72 173 (Polychromatic418967fa.accept_13_11_7_4_1_1561 50 72 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 72 173 (accept_3_2 49 72 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 72 173 (Polychromatic418967fa.accept_13_9_7_4_1_953 48 72 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 72 173
  (Polychromatic418967fa.accept_11_3_6_8_1_1924 47 72 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 72 173 (accept_3_2 46 72 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  72 173 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 72 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 72 173 (Polychromatic418967fa.accept_16_12_8_13_1_6073 44 72 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 173 (accept_3_2 43 72 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 72 173 (Polychromatic418967fa.accept_13_3_7_4_1_435 42 72 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 72 173
  (Polychromatic418967fa.accept_10_1_2_3_1_1910 41 72 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 72 173 (accept_3_2 40 72 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  72 173 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 72 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 72 173 (Polychromatic418967fa.accept_7_3_2_5_1_147 38 72 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 173 (accept_3_2 37 72 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 72 173 (Polychromatic418967fa.accept_11_3_6_8_1_1924 36 72 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 72 173
  (Polychromatic418967fa.accept_10_5_2_3_1_239 35 72 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 72 173 (accept_3_2 34 72 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  72 173 (Polychromatic418967fa.accept_15_3_12_8_1_738 33 72 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 72 173 (Polychromatic418967fa.accept_7_4_2_5_1_527 32 72 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 72 173 (accept_3_2 31 72 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 72 173 (Polychromatic418967fa.accept_17_13_4_3_1_1446 30 72 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 72 173
  (Polychromatic418967fa.accept_13_3_7_4_1_435 29 72 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 72 173 (accept_3_2 28 72 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  72 173 (Polychromatic418967fa.accept_16_11_8_13_1_3844 27 72 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 72 173 (Polychromatic418967fa.accept_15_11_12_8_1_739 26 72 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 173 (accept_3_2 25 72 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 72 173 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 72 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 72 173
  (Polychromatic418967fa.accept_13_10_7_4_1_2262 23 72 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 72 173 (accept_3_2 22 72 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  72 173 (Polychromatic418967fa.accept_10_1_2_3_1_1910 21 72 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 72 173 (Polychromatic418967fa.accept_15_5_12_8_1_3168 20 72 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 173 (accept_3_2 19 72 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 72 173 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 72 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 72 173
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 72 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 72 173 (accept_3_2 16 72 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  72 173 (Polychromatic418967fa.accept_10_5_2_3_1_239 15 72 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 72 173 (Polychromatic418967fa.accept_11_3_6_8_1_1924 14 72 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 173 (accept_3_2 13 72 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 72 173 (Polychromatic418967fa.accept_13_12_7_4_1_3124 12 72 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 72 173
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 72 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 72 173 (accept_3_2 10 72 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  72 173 (Polychromatic418967fa.accept_13_9_7_4_1_953 9 72 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 72 173 (Polychromatic418967fa.accept_19_8_15_2_1_6961 8 72 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 173 (accept_3_2 7 72 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 72 173 (Polychromatic418967fa.accept_13_6_7_4_1_2264 6 72 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 72 173
  (Polychromatic418967fa.accept_10_5_2_3_1_239 5 72 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 72 173 (accept_3_2 4 72 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 72
  173 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 72 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 72 173 (Polychromatic418967fa.accept_22_2_6_19_1_6438 2 72 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 173 (accept_3_2 1 72 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 72 173)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 173
  (allA_succ_of_accept 70 71 173 (accept_3_2 70 71 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  71 173 (Polychromatic418967fa.accept_7_6_1_5_1_322 69 71 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 71 173 (Polychromatic418967fa.accept_9_5_8_2_1_409 68 71 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 173 (accept_3_2 67 71 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 71 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 173
  (Polychromatic418967fa.accept_15_5_11_8_1_1391 65 71 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 173 (accept_3_2 64 71 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 173 (Polychromatic418967fa.accept_13_11_6_4_1_3121 63 71 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 71 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 173 (accept_3_2 61 71 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 173 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 71 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 173
  (Polychromatic418967fa.accept_7_3_1_5_1_44 59 71 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 173 (accept_3_2 58 71 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 173 (Polychromatic418967fa.accept_9_3_8_2_1_162 57 71 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 173 (Polychromatic418967fa.accept_18_2_17_11_1_3178 56 71 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 173 (accept_3_2 55 71 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 71 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 173
  (Polychromatic418967fa.accept_7_4_1_5_1_540 53 71 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 173 (accept_3_2 52 71 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 173 (Polychromatic418967fa.accept_9_6_8_2_1_410 51 71 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 71 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 173 (accept_3_2 49 71 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 173 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 71 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 173
  (Polychromatic418967fa.accept_11_3_5_8_1_458 47 71 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 173 (accept_3_2 46 71 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 173 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 71 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 173 (Polychromatic418967fa.accept_13_5_6_4_1_1582 44 71 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 173 (accept_3_2 43 71 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 71 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 173
  (Polychromatic418967fa.accept_7_6_1_5_1_322 41 71 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 173 (accept_3_2 40 71 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 173 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 71 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 71 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 173 (accept_3_2 37 71 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 173 (Polychromatic418967fa.accept_11_3_5_8_1_458 36 71 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 173
  (Polychromatic418967fa.accept_11_2_5_8_1_470 35 71 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 173 (accept_3_2 34 71 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 173 (Polychromatic418967fa.accept_9_6_8_2_1_410 33 71 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 173 (Polychromatic418967fa.accept_7_4_1_5_1_540 32 71 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 173 (accept_3_2 31 71 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 71 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 173
  (Polychromatic418967fa.accept_23_6_2_12_1_9765 29 71 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 173 (accept_3_2 28 71 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 173 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 71 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 71 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 173 (accept_3_2 25 71 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 173 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 71 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 173
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 71 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 173 (accept_3_2 22 71 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 173 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 71 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 173 (Polychromatic418967fa.accept_7_6_1_5_1_322 20 71 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 173 (accept_3_2 19 71 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 71 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 173
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 71 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 173 (accept_3_2 16 71 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 173 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 71 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 71 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 173 (accept_3_2 13 71 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 173 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 71 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 173
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 71 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 173 (accept_3_2 10 71 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 173 (Polychromatic418967fa.accept_13_9_6_4_1_2243 9 71 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 173 (Polychromatic418967fa.accept_10_8_1_3_1_1374 8 71 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 173 (accept_3_2 7 71 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 71 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 173
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 71 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 173 (accept_3_2 4 71 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  173 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 71 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 71 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 173 (accept_3_2 1 71 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 173))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 173
  (allA_of_3_0 70 70 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 69 173 (allA_succ_of_accept 68 69 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 69 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 69 173 (accept_3_2 67 69 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  69 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 69 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 69 173 (Polychromatic418967fa.accept_16_1_5_13_1_1025 65 69 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 173 (accept_3_2 64 69 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 173 (Polychromatic418967fa.accept_12_3_9_5_1_853 63 69 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 69 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 69 173 (accept_3_2 61 69 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  69 173 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 69 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 69 173 (Polychromatic418967fa.accept_9_5_6_2_1_161 59 69 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 173 (accept_3_2 58 69 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 173 (Polychromatic418967fa.accept_7_1_6_5_1_39 57 69 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 69 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 173 (accept_3_2 55 69 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  69 173 (Polychromatic418967fa.accept_10_4_9_3_1_1907 54 69 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 69 173 (Polychromatic418967fa.accept_7_4_6_5_1_141 53 69 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 173 (accept_3_2 52 69 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 173 (Polychromatic418967fa.accept_12_3_9_5_1_853 51 69 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 69 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 69 173 (accept_3_2 49 69 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  69 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 69 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 69 173 (Polychromatic418967fa.accept_15_2_9_8_1_736 47 69 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 173 (accept_3_2 46 69 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 173 (Polychromatic418967fa.accept_18_9_15_11_1_5693 45 69 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 69 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 69 173 (accept_3_2 43 69 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  69 173 (Polychromatic418967fa.accept_16_10_5_13_1_8591 42 69 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 69 173 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 69 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 173 (accept_3_2 40 69 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 173 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 69 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 69 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 173 (accept_3_2 37 69 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  69 173 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 69 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 69 173 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 69 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 173 (accept_3_2 34 69 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 173 (Polychromatic418967fa.accept_15_3_9_8_1_3164 33 69 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 69 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 173 (accept_3_2 31 69 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  69 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 69 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 69 173 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 69 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 173 (accept_3_2 28 69 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 173 (Polychromatic418967fa.accept_11_5_3_8_1_454 27 69 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 69 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 69 173 (accept_3_2 25 69 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  69 173 (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 69 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 69 173 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 69 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 173 (accept_3_2 22 69 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 69 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 69 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 173 (accept_3_2 19 69 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  69 173 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 69 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 69 173 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 69 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 173 (accept_3_2 16 69 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 173 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 69 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 69 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 173 (accept_3_2 13 69 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  69 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 69 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 69 173 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 69 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 173 (accept_3_2 10 69 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 173 (Polychromatic418967fa.accept_16_9_5_13_1_4972 9 69 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 69 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 173 (accept_3_2 7 69 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69
  173 (Polychromatic418967fa.accept_10_6_9_3_1_935 6 69 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 173 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 69 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 173 (accept_3_2 4 69 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 69 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 69 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 69
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 173 (accept_3_2 1 69 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  173))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 173 (allA_succ_of_accept 67 68
  173 (accept_3_2 67 68 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 68 173
  (Polychromatic418967fa.accept_9_3_5_2_1_28 66 68 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 68 173 (Polychromatic418967fa.accept_8_1_4_5_1_48 65 68 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 68 173 (accept_3_2 64 68 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 68 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 68 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 68 173 (Polychromatic418967fa.accept_9_8_5_2_1_422 62
  68 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 68 173 (accept_3_2 61 68
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 68 173
  (Polychromatic418967fa.accept_9_6_5_2_1_421 60 68 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 68 173 (Polychromatic418967fa.accept_13_7_3_4_1_459 59 68 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 68 173 (accept_3_2 58 68 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 68 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 68 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 68 173 (Polychromatic418967fa.accept_10_6_8_3_1_930
  56 68 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 68 173 (accept_3_2 55
  68 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 68 173
  (Polychromatic418967fa.accept_16_6_4_13_1_3841 54 68 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 68 173 (Polychromatic418967fa.accept_9_8_5_2_1_422 53 68 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 68 173 (accept_3_2 52 68 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 68 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 68 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 68 173 (Polychromatic418967fa.accept_12_2_8_5_1_408
  50 68 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 68 173 (accept_3_2 49
  68 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 68 173
  (Polychromatic418967fa.accept_9_3_5_2_1_28 48 68 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 68 173 (Polychromatic418967fa.accept_19_9_11_2_1_5436 47 68 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 68 173 (accept_3_2 46 68 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 68 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 68 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 68 173 (Polychromatic418967fa.accept_9_8_5_2_1_422 44
  68 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 68 173 (accept_3_2 43 68
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 68 173
  (Polychromatic418967fa.accept_9_6_5_2_1_421 42 68 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 68 173 (Polychromatic418967fa.accept_8_1_4_5_1_48 41 68 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 68 173 (accept_3_2 40 68 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 68 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 68 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 68 173 (Polychromatic418967fa.accept_11_5_2_8_1_866
  38 68 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 68 173 (accept_3_2 37
  68 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 68 173
  (Polychromatic418967fa.accept_10_6_8_3_1_930 36 68 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 68 173 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 68 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 68 173 (accept_3_2 34 68 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 68 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 68 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 173
  (Polychromatic418967fa.accept_19_13_11_2_1_4112 32 68 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 68 173 (accept_3_2 31 68 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  68 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 68 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 68 173 (Polychromatic418967fa.accept_19_10_11_2_1_8354 29 68 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 68 173 (accept_3_2 28 68 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 68 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 68 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 68 173
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 68 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 68 173 (accept_3_2 25 68 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  68 173 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 68 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 68 173 (Polychromatic418967fa.accept_16_7_4_13_1_1057 23 68 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 68 173 (accept_3_2 22 68 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 68 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 68 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 68 173
  (Polychromatic418967fa.accept_13_7_3_4_1_459 20 68 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 68 173 (accept_3_2 19 68 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  68 173 (Polychromatic418967fa.accept_20_18_8_13_1_6761 18 68 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 68 173 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 68 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 68 173 (accept_3_2 16 68 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 68 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 68 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 68 173
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 68 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 68 173 (accept_3_2 13 68 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  68 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 68 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 68 173 (Polychromatic418967fa.accept_10_1_8_3_1_947 11 68 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 68 173 (accept_3_2 10 68 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 68 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 68 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 68 173
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 68 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 68 173 (accept_3_2 7 68 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 68
  173 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 68 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 68 173 (Polychromatic418967fa.accept_10_5_8_3_1_229 5 68 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 68 173 (accept_3_2 4 68 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 68 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 68 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 68 173 (Polychromatic418967fa.accept_12_2_8_5_1_408 2
  68 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 173 (accept_3_2 1 68 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  173)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 173 (allA_of_3_0 67 67 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 66 173 (allA_succ_of_accept 65 66 173
  (Polychromatic418967fa.accept_7_2_3_5_1_34 65 66 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 66 173 (accept_3_2 64 66 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  66 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 66 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 66 173 (Polychromatic418967fa.accept_9_8_3_2_1_417 62 66 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 66 173 (accept_3_2 61 66 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 66 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 66 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 66 173
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 66 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 66 173 (accept_3_2 58 66 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  66 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 66 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 66 173 (Polychromatic418967fa.accept_19_18_9_2_1_9764 56 66 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 66 173 (accept_3_2 55 66 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 66 173 (Polychromatic418967fa.accept_14_12_10_5_1_2712 54 66
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 66 173
  (Polychromatic418967fa.accept_9_8_3_2_1_417 53 66 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 66 173 (accept_3_2 52 66 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  66 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 66 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 66 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 50 66 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 173 (accept_3_2 49 66 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 66 173 (Polychromatic418967fa.accept_10_8_6_3_1_1394 48 66 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 66 173
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 66 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 66 173 (accept_3_2 46 66 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  66 173 (Polychromatic418967fa.accept_18_9_12_11_1_5642 45 66 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 66 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 44 66 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 66 173 (accept_3_2 43 66 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 66 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 66 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 66 173
  (Polychromatic418967fa.accept_9_5_3_2_1_171 41 66 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 66 173 (accept_3_2 40 66 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  66 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 66 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 66 173 (Polychromatic418967fa.accept_10_8_6_3_1_1394 38 66 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 66 173 (accept_3_2 37 66 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 66 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 66 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 66 173
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 66 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 66 173 (accept_3_2 34 66 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  66 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 66 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 66 173 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 66 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 173 (accept_3_2 31 66 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 66 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 66 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 66 173
  (Polychromatic418967fa.accept_7_1_3_5_1_33 29 66 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 66 173 (accept_3_2 28 66 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  66 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 66 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 66 173 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 66 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 173 (accept_3_2 25 66 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 66 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 66 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 66 173
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 66 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 66 173 (accept_3_2 22 66 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  66 173 (Polychromatic418967fa.accept_16_5_2_13_1_1007 21 66 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 66 173 (Polychromatic418967fa.accept_19_1_9_2_1_6945 20 66 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 173 (accept_3_2 19 66 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 66 173 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 66 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 66 173
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 66 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 66 173 (accept_3_2 16 66 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  66 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 66 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 66 173 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 66 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 173 (accept_3_2 13 66 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 66 173 (Polychromatic418967fa.accept_14_12_10_5_1_2712 12 66 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 66 173
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 66 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 66 173 (accept_3_2 10 66 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  66 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 66 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 66 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 66 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 173 (accept_3_2 7 66 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 66 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 66 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 66 173
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 66 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 66 173 (accept_3_2 4 66 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 66
  173 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 66 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 66 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 66 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 173 (accept_3_2 1 66 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 66 173)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 173
  (allA_succ_of_accept 64 65 173 (accept_3_2 64 65 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  65 173 (Polychromatic418967fa.accept_14_7_9_5_1_529 63 65 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 65 173 (Polychromatic418967fa.accept_10_2_5_3_1_1408 62 65 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 173 (accept_3_2 61 65 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 65 173 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 65 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 173
  (Polychromatic418967fa.accept_7_3_2_5_1_147 59 65 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 65 173 (accept_3_2 58 65 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  65 173 (Polychromatic418967fa.accept_10_7_5_3_1_542 57 65 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 65 173 (Polychromatic418967fa.accept_15_11_5_8_1_3157 56 65 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 173 (accept_3_2 55 65 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 65 173 (Polychromatic418967fa.accept_23_8_19_12_1_9763 54 65
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 173
  (Polychromatic418967fa.accept_7_4_2_5_1_527 53 65 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 65 173 (accept_3_2 52 65 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  65 173 (Polychromatic418967fa.accept_16_3_1_13_1_4968 51 65 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 65 173 (Polychromatic418967fa.accept_20_10_5_13_1_6727 50 65 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 173 (accept_3_2 49 65 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 173 (Polychromatic418967fa.accept_10_8_5_3_1_543 48 65 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 173
  (Polychromatic418967fa.accept_10_7_5_3_1_542 47 65 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 65 173 (accept_3_2 46 65 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  65 173 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 65 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 65 173 (Polychromatic418967fa.accept_8_4_1_5_1_186 44 65 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 173 (accept_3_2 43 65 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 173 (Polychromatic418967fa.accept_10_2_5_3_1_1408 42 65 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 173
  (Polychromatic418967fa.accept_15_11_5_8_1_3157 41 65 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 65 173 (accept_3_2 40 65 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  65 173 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 65 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 65 173 (Polychromatic418967fa.accept_7_3_2_5_1_147 38 65 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 173 (accept_3_2 37 65 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 173 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 65 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 173
  (Polychromatic418967fa.accept_14_7_9_5_1_529 35 65 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 65 173 (accept_3_2 34 65 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  65 173 (Polychromatic418967fa.accept_15_3_5_8_1_1387 33 65 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 173 (Polychromatic418967fa.accept_7_4_2_5_1_527 32 65 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 173 (accept_3_2 31 65 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 65 173 (Polychromatic418967fa.accept_16_14_1_13_1_2754 30 65 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 173
  (Polychromatic418967fa.accept_15_14_5_8_1_3175 29 65 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 173 (accept_3_2 28 65 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  65 173 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 65 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 65 173 (Polychromatic418967fa.accept_15_11_5_8_1_3157 26 65 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 173 (accept_3_2 25 65 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 173 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 65 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 173
  (Polychromatic418967fa.accept_17_6_14_3_1_4678 23 65 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 173 (accept_3_2 22 65 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 173 (Polychromatic418967fa.accept_14_7_9_5_1_529 21 65 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 173 (Polychromatic418967fa.accept_8_4_1_5_1_186 20 65 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 173 (accept_3_2 19 65 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 173 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 65 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 173
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 65 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 173 (accept_3_2 16 65 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 173 (Polychromatic418967fa.accept_17_15_14_3_1_5947 15 65 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 173 (Polychromatic418967fa.accept_15_14_5_8_1_3175 14 65 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 173 (accept_3_2 13 65 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 173 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 65 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 173
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 65 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 173 (accept_3_2 10 65 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 173 (Polychromatic418967fa.accept_11_9_10_8_1_444 9 65 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 173 (Polychromatic418967fa.accept_10_8_5_3_1_543 8 65 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 173 (accept_3_2 7 65 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 173 (Polychromatic418967fa.accept_17_6_14_3_1_4678 6 65 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 173
  (Polychromatic418967fa.accept_16_5_1_13_1_1053 5 65 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 173 (accept_3_2 4 65 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  173 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 65 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 173 (Polychromatic418967fa.accept_10_2_5_3_1_1408 2 65 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 173 (accept_3_2 1 65 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 173))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 173
  (allA_of_3_0 64 64 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 63 173 (allA_succ_of_accept 62 63 173
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 63 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 173 (accept_3_2 61 63 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  63 173 (Polychromatic418967fa.accept_13_8_11_4_1_1553 60 63 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 63 173 (Polychromatic418967fa.accept_13_7_11_4_1_2247 59 63 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 173 (accept_3_2 58 63 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 173 (Polychromatic418967fa.accept_12_9_3_5_1_423 57 63 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 63 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 63 173 (accept_3_2 55 63 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  63 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 63 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 63 173 (Polychromatic418967fa.accept_19_15_6_2_1_6865 53 63 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 173 (accept_3_2 52 63 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 173 (Polychromatic418967fa.accept_13_12_11_4_1_3111 51 63
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 173
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 63 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 173 (accept_3_2 49 63 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  63 173 (Polychromatic418967fa.accept_18_12_9_11_1_4370 48 63 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 63 173 (Polychromatic418967fa.accept_13_8_11_4_1_1553 47 63 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 173 (accept_3_2 46 63 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 173 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 63 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 63 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 173 (accept_3_2 43 63 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  63 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 63 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 63 173 (Polychromatic418967fa.accept_13_2_11_4_1_445 41 63 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 173 (accept_3_2 40 63 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 173 (Polychromatic418967fa.accept_15_9_3_8_1_3155 39 63 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 173
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 63 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 173 (accept_3_2 37 63 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  63 173 (Polychromatic418967fa.accept_13_10_11_4_1_2248 36 63 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 63 173 (Polychromatic418967fa.accept_15_5_3_8_1_748 35 63 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 173 (accept_3_2 34 63 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 173 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 63 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 63 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 173 (accept_3_2 31 63 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  63 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 63 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 63 173 (Polychromatic418967fa.accept_19_10_6_2_1_6907 29 63 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 173 (accept_3_2 28 63 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 173 (Polychromatic418967fa.accept_15_12_3_8_1_5245 27 63
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 173
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 63 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 173 (accept_3_2 25 63 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  63 173 (Polychromatic418967fa.accept_15_9_3_8_1_3155 24 63 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 63 173 (Polychromatic418967fa.accept_13_10_11_4_1_2248 23 63 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 173 (accept_3_2 22 63 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 173 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 63 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 63 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 173 (accept_3_2 19 63 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  63 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 63 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 63 173 (Polychromatic418967fa.accept_29_17_5_28_1_9762 17 63 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 173 (accept_3_2 16 63 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 173 (Polychromatic418967fa.accept_13_2_11_4_1_445 15 63 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 173
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 63 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 173 (accept_3_2 13 63 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  63 173 (Polychromatic418967fa.accept_13_12_11_4_1_3111 12 63 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 63 173 (Polychromatic418967fa.accept_15_11_3_8_1_750 11 63 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 173 (accept_3_2 10 63 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 173 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 63 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 63 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 173 (accept_3_2 7 63 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63
  173 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 63 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 173 (Polychromatic418967fa.accept_15_5_3_8_1_748 5 63 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 173 (accept_3_2 4 63 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 63 173 (Polychromatic418967fa.accept_16_3_15_13_1_2825 3 63 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 63
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 173 (accept_3_2 1 63 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  173))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 173 (allA_succ_of_accept 61 62 173
  (accept_3_2 61 62 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 62 173
  (Polychromatic418967fa.accept_7_4_6_5_1_141 60 62 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 62 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 62 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 62 173 (accept_3_2 58 62 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 62 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 62 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 62 173 (Polychromatic418967fa.accept_12_8_2_5_1_844
  56 62 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 62 173 (accept_3_2 55
  62 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 62 173
  (Polychromatic418967fa.accept_15_9_2_8_1_1379 54 62 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 62 173 (Polychromatic418967fa.accept_7_4_6_5_1_141 53 62 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 62 173 (accept_3_2 52 62 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 62 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 62 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 62 173 (Polychromatic418967fa.accept_7_1_6_5_1_39 50
  62 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 62 173 (accept_3_2 49 62
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 62 173
  (Polychromatic418967fa.accept_9_3_8_2_1_162 48 62 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 62 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 62 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 62 173 (accept_3_2 46 62 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 62 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 62 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 62 173 (Polychromatic418967fa.accept_12_8_2_5_1_844
  44 62 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 62 173 (accept_3_2 43
  62 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 62 173
  (Polychromatic418967fa.accept_9_6_8_2_1_410 42 62 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 62 173 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 62 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 62 173 (accept_3_2 40 62 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 62 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 62 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 62 173
  (Polychromatic418967fa.accept_20_18_2_13_1_5265 38 62 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 62 173 (accept_3_2 37 62 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  62 173 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 62 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 62 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 62 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 62 173 (accept_3_2 34 62 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 62 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 62 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 62 173
  (Polychromatic418967fa.accept_7_4_6_5_1_141 32 62 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 62 173 (accept_3_2 31 62 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  62 173 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 62 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 62 173 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 62 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 62 173 (accept_3_2 28 62 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 62 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 62 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 62 173
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 26 62 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 62 173 (accept_3_2 25 62 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  62 173 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 62 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 62 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 62 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 62 173 (accept_3_2 22 62 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 62 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 62 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 62 173
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 62 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 62 173 (accept_3_2 19 62 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  62 173 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 62 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 62 173 (Polychromatic418967fa.accept_16_1_14_13_1_3834 17 62 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 62 173 (accept_3_2 16 62 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 62 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 62 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 62 173
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 62 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 62 173 (accept_3_2 13 62 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  62 173 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 62 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 62 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 62 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 62 173 (accept_3_2 10 62 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 62 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 62 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 62 173
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 62 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 62 173 (accept_3_2 7 62 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 62
  173 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 62 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 62 173 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 62 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 62 173 (accept_3_2 4 62 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 62 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 62 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 62 173 (Polychromatic418967fa.accept_17_2_11_3_1_4654
  2 62 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 173 (accept_3_2 1 62
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  173)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 173 (allA_of_3_0 61 61 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 60 173 (allA_succ_of_accept 59 60 173
  (Polychromatic418967fa.accept_9_5_6_2_1_161 59 60 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 60 173 (accept_3_2 58 60 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  60 173 (Polychromatic418967fa.accept_7_1_4_5_1_35 57 60 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 60 173 (Polychromatic418967fa.accept_16_8_12_13_1_3851 56 60 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 60 173 (accept_3_2 55 60 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 60 173 (Polychromatic418967fa.accept_19_16_3_2_1_6964 54 60
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 60 173
  (Polychromatic418967fa.accept_9_8_6_2_1_744 53 60 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 60 173 (accept_3_2 52 60 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  60 173 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 60 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 60 173 (Polychromatic418967fa.accept_7_1_4_5_1_35 50 60 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 60 173 (accept_3_2 49 60 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 60 173 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 60 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 60 173
  (Polychromatic418967fa.accept_11_3_5_8_1_458 47 60 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 60 173 (accept_3_2 46 60 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  60 173 (Polychromatic418967fa.accept_17_11_9_3_1_1463 45 60 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 60 173 (Polychromatic418967fa.accept_7_2_4_5_1_313 44 60 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 173 (accept_3_2 43 60 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 60 173 (Polychromatic418967fa.accept_16_10_12_13_1_4950 42 60 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 60 173
  (Polychromatic418967fa.accept_7_6_4_5_1_314 41 60 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 60 173 (accept_3_2 40 60 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  60 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 60 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 60 173 (Polychromatic418967fa.accept_13_12_8_4_1_3099 38 60 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 173 (accept_3_2 37 60 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 60 173 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 60 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 60 173
  (Polychromatic418967fa.accept_9_8_6_2_1_744 35 60 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 60 173 (accept_3_2 34 60 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  60 173 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 60 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 60 173 (Polychromatic418967fa.accept_9_5_6_2_1_161 32 60 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 173 (accept_3_2 31 60 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 60 173 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 60 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 60 173
  (Polychromatic418967fa.accept_7_1_4_5_1_35 29 60 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 60 173 (accept_3_2 28 60 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  60 173 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 60 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 60 173 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 60 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 60 173 (accept_3_2 25 60 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 60 173 (Polychromatic418967fa.accept_11_2_5_8_1_470 24 60 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 60 173
  (Polychromatic418967fa.accept_7_2_4_5_1_313 23 60 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 60 173 (accept_3_2 22 60 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  60 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 60 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 60 173 (Polychromatic418967fa.accept_7_6_4_5_1_314 20 60 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 173 (accept_3_2 19 60 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 60 173 (Polychromatic418967fa.accept_17_1_9_3_1_7161 18 60 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 60 173
  (Polychromatic418967fa.accept_8_1_4_5_1_48 17 60 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 60 173 (accept_3_2 16 60 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  60 173 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 60 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 60 173 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 60 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 173 (accept_3_2 13 60 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 60 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 60 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 60 173
  (Polychromatic418967fa.accept_13_11_8_4_1_3950 11 60 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 60 173 (accept_3_2 10 60 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  60 173 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 60 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 60 173 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 60 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 173 (accept_3_2 7 60 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 60 173 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 60 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 60 173
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 60 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 60 173 (accept_3_2 4 60 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 60
  173 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 60 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 60 173 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 60 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 173 (accept_3_2 1 60 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 60 173)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 173
  (allA_succ_of_accept 58 59 173 (accept_3_2 58 59 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  59 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 59 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 59 173 (Polychromatic418967fa.accept_10_6_9_3_1_935 56 59 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 173 (accept_3_2 55 59 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 59 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 59 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 173
  (Polychromatic418967fa.accept_9_8_5_2_1_422 53 59 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 173 (accept_3_2 52 59 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 59 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 59 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 173 (accept_3_2 49 59 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 59 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 173
  (Polychromatic418967fa.accept_17_13_8_3_1_7177 47 59 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 173 (accept_3_2 46 59 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 173 (Polychromatic418967fa.accept_11_1_4_8_1_1918 45 59 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 44 59 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 173 (accept_3_2 43 59 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 59 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 173
  (Polychromatic418967fa.accept_23_18_13_12_1_9761 41 59 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 59 173 (accept_3_2 40 59 173 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 59 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 59 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 59 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 59 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 173 (accept_3_2 37 59 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 36
  59 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 173
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 59 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 173 (accept_3_2 34 59 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 173 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 59 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 173 (Polychromatic418967fa.accept_13_6_7_4_1_2264 32 59 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 173 (accept_3_2 31 59 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 59 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 173
  (Polychromatic418967fa.accept_7_1_3_5_1_33 29 59 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 173 (accept_3_2 28 59 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 173 (Polychromatic418967fa.accept_25_2_9_23_1_9760 27 59 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 59 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 173 (accept_3_2 25 59 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 173 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 59 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 173
  (Polychromatic418967fa.accept_7_2_3_5_1_34 23 59 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 173 (accept_3_2 22 59 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 59 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 173 (Polychromatic418967fa.accept_15_5_14_8_1_1376 20 59 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 173 (accept_3_2 19 59 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 59 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 173
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 59 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 173 (accept_3_2 16 59 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 59 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 59 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 173 (accept_3_2 13 59 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 59 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 173
  (Polychromatic418967fa.accept_13_11_7_4_1_1561 11 59 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 173 (accept_3_2 10 59 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 59 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 59 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 173 (accept_3_2 7 59 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 59 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 173
  (Polychromatic418967fa.accept_15_5_14_8_1_1376 5 59 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 173 (accept_3_2 4 59 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  173 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 59 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 59 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 59 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 173 (accept_3_2 1 59 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 59 173))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 173 (allA_of_3_0
  58 58 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 57 173 (allA_succ_of_accept 56 57 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 57 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 173 (accept_3_2 55 57 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  57 173 (Polychromatic418967fa.accept_10_4_7_3_1_54 54 57 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 57 173 (Polychromatic418967fa.accept_7_4_1_5_1_540 53 57 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 173 (accept_3_2 52 57 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 57 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 57 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 173 (accept_3_2 49 57 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  57 173 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 57 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 57 173 (Polychromatic418967fa.accept_23_1_11_12_1_6314 47 57 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 173 (accept_3_2 46 57 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 173 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 57 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 57 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 173 (accept_3_2 43 57 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  57 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 57 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 57 173 (Polychromatic418967fa.accept_7_6_1_5_1_322 41 57 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 173 (accept_3_2 40 57 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 173 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 57 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 57 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 173 (accept_3_2 37 57 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  57 173 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 57 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 57 173 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 57 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 173 (accept_3_2 34 57 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 57 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 57 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 173 (accept_3_2 31 57 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  57 173 (Polychromatic418967fa.accept_20_10_17_13_1_6773 30 57 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 57 173 (Polychromatic418967fa.accept_21_8_15_5_1_8178 29 57 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 173 (accept_3_2 28 57 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 173 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 57 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 57 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 173 (accept_3_2 25 57 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  57 173 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 57 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 57 173 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 57 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 173 (accept_3_2 22 57 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 173 (Polychromatic418967fa.accept_16_5_9_13_1_3845 21 57 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 57 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 173 (accept_3_2 19 57 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  57 173 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 57 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 57 173 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 57 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 173 (accept_3_2 16 57 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 57 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 57 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 173 (accept_3_2 13 57 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  57 173 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 57 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 57 173 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 57 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 173 (accept_3_2 10 57 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 173 (Polychromatic418967fa.accept_13_9_5_4_1_1591 9 57 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 57 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 173 (accept_3_2 7 57 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57
  173 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 57 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 173 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 57 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 173 (accept_3_2 4 57 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 173 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 57 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 57
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 173 (accept_3_2 1 57 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 173)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 173 (allA_succ_of_accept 55 56 173 (accept_3_2 55 56 173 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 56 173 (Polychromatic418967fa.accept_19_16_18_2_1_6934 54 56 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 56 173 (Polychromatic418967fa.accept_16_5_8_13_1_2764 53 56
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 173 (accept_3_2 52 56 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 56 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 51
  56 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 56 173
  (Polychromatic418967fa.accept_12_2_8_5_1_408 50 56 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 56 173 (accept_3_2 49 56 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  56 173 (Polychromatic418967fa.accept_10_8_6_3_1_1394 48 56 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 56 173 (Polychromatic418967fa.accept_10_7_6_3_1_927 47 56 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 173 (accept_3_2 46 56 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 56 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 56 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 173
  (Polychromatic418967fa.accept_16_12_8_13_1_6073 44 56 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 56 173 (accept_3_2 43 56 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  56 173 (Polychromatic418967fa.accept_15_12_11_8_1_1392 42 56 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 56 173 (Polychromatic418967fa.accept_19_3_18_2_1_6935 41 56 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 56 173 (accept_3_2 40 56 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 56 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 56 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 173
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 38 56 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 56 173 (accept_3_2 37 56 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  56 173 (Polychromatic418967fa.accept_16_4_8_13_1_1059 36 56 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 56 173 (Polychromatic418967fa.accept_15_5_11_8_1_1391 35 56 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 56 173 (accept_3_2 34 56 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 56 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 56 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 56 173
  (Polychromatic418967fa.accept_18_14_2_11_1_4384 32 56 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 56 173 (accept_3_2 31 56 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  56 173 (Polychromatic418967fa.accept_21_9_14_5_1_8160 30 56 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 56 173 (Polychromatic418967fa.accept_10_9_6_3_1_545 29 56 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 56 173 (accept_3_2 28 56 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 56 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 56 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 173
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 26 56 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 56 173 (accept_3_2 25 56 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  56 173 (Polychromatic418967fa.accept_19_5_18_2_1_5404 24 56 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 56 173 (Polychromatic418967fa.accept_17_6_5_3_1_7134 23 56 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 173 (accept_3_2 22 56 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 56 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 56 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 56 173
  (Polychromatic418967fa.accept_15_5_11_8_1_1391 20 56 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 56 173 (accept_3_2 19 56 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  56 173 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 56 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 56 173 (Polychromatic418967fa.accept_10_7_6_3_1_927 17 56 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 173 (accept_3_2 16 56 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 56 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 56 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 56 173
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 56 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 56 173 (accept_3_2 13 56 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  56 173 (Polychromatic418967fa.accept_15_12_11_8_1_1392 12 56 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 56 173 (Polychromatic418967fa.accept_16_11_8_13_1_3844 11 56 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 173 (accept_3_2 10 56 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 56 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 56 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 173
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 8 56 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 56 173 (accept_3_2 7 56 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 56
  173 (Polychromatic418967fa.accept_17_6_5_3_1_7134 6 56 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 56 173 (Polychromatic418967fa.accept_15_5_11_8_1_1391 5 56 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 173 (accept_3_2 4 56 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 56 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 56 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 173
  (Polychromatic418967fa.accept_12_2_8_5_1_408 2 56 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 56 173 (accept_3_2 1 56 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56
  173)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 55 173 (allA_of_3_0 55 55 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 54 173 (allA_succ_of_accept 53 54 173
  (Polychromatic418967fa.accept_11_9_10_8_1_444 53 54 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 54 173 (accept_3_2 52 54 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  54 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 54 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 54 173 (Polychromatic418967fa.accept_13_11_2_4_1_1590 50 54 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 173 (accept_3_2 49 54 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 173 (Polychromatic418967fa.accept_15_3_9_8_1_3164 48 54 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 54 173
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 54 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 54 173 (accept_3_2 46 54 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  54 173 (Polychromatic418967fa.accept_13_6_2_4_1_923 45 54 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 54 173 (Polychromatic418967fa.accept_13_5_2_4_1_3955 44 54 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 173 (accept_3_2 43 54 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 173 (Polychromatic418967fa.accept_11_9_10_8_1_444 42 54 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 54 173
  (Polychromatic418967fa.accept_16_9_6_13_1_3831 41 54 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 54 173 (accept_3_2 40 54 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  54 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 54 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 54 173 (Polychromatic418967fa.accept_13_12_2_4_1_3131 38 54 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 173 (accept_3_2 37 54 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 54 173 (Polychromatic418967fa.accept_16_4_6_13_1_1874 36 54
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 54 173
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 54 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 54 173 (accept_3_2 34 54 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  54 173 (Polychromatic418967fa.accept_15_3_9_8_1_3164 33 54 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 54 173 (Polychromatic418967fa.accept_13_6_2_4_1_923 32 54 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 173 (accept_3_2 31 54 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 54 173 (Polychromatic418967fa.accept_19_11_16_2_1_9759 30 54 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 54 173
  (Polychromatic418967fa.accept_10_9_4_3_1_539 29 54 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 54 173 (accept_3_2 28 54 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  54 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 54 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 54 173 (Polychromatic418967fa.accept_19_7_16_2_1_6953 26 54 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 173 (accept_3_2 25 54 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 54 173 (Polychromatic418967fa.accept_13_11_2_4_1_1590 24 54
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 54 173
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 54 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 54 173 (accept_3_2 22 54 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  54 173 (Polychromatic418967fa.accept_14_7_12_5_1_1861 21 54 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 54 173 (Polychromatic418967fa.accept_11_9_10_8_1_444 20 54 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 173 (accept_3_2 19 54 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 54 173 (Polychromatic418967fa.accept_13_5_2_4_1_3955 18 54 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 54 173
  (Polychromatic418967fa.accept_10_7_4_3_1_560 17 54 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 54 173 (accept_3_2 16 54 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  54 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 54 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 54 173 (Polychromatic418967fa.accept_15_14_9_8_1_3165 14 54 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 173 (accept_3_2 13 54 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 54 173 (Polychromatic418967fa.accept_13_12_2_4_1_3131 12 54
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 54 173
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 54 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 54 173 (accept_3_2 10 54 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  54 173 (Polychromatic418967fa.accept_10_9_4_3_1_539 9 54 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 54 173 (Polychromatic418967fa.accept_20_8_14_13_1_8213 8 54 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 173 (accept_3_2 7 54 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 54 173 (Polychromatic418967fa.accept_13_6_2_4_1_923 6 54 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 54 173
  (Polychromatic418967fa.accept_13_5_2_4_1_3955 5 54 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 54 173 (accept_3_2 4 54 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 54
  173 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 54 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 54 173 (Polychromatic418967fa.accept_15_2_9_8_1_736 2 54 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 173 (accept_3_2 1 54 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 54 173)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 173
  (allA_succ_of_accept 52 53 173 (accept_3_2 52 53 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  53 173 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 53 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 53 173 (Polychromatic418967fa.accept_7_1_4_5_1_35 50 53 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 173 (accept_3_2 49 53 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 53 173 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 53 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 173
  (Polychromatic418967fa.accept_19_9_15_2_1_9758 47 53 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 53 173 (accept_3_2 46 53 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  53 173 (Polychromatic418967fa.accept_17_11_2_3_1_8468 45 53 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 53 173 (Polychromatic418967fa.accept_7_2_4_5_1_313 44 53 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 173 (accept_3_2 43 53 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 53 173 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 53 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 173
  (Polychromatic418967fa.accept_7_6_4_5_1_314 41 53 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 173 (accept_3_2 40 53 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 173 (Polychromatic418967fa.accept_9_3_8_2_1_162 39 53 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 173 (Polychromatic418967fa.accept_18_2_17_11_1_3178 38 53 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 173 (accept_3_2 37 53 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 173 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 53 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 173
  (Polychromatic418967fa.accept_17_1_2_3_1_4668 35 53 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 173 (accept_3_2 34 53 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 173 (Polychromatic418967fa.accept_9_6_8_2_1_410 33 53 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 173 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 53 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 173 (accept_3_2 31 53 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 173 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 53 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 173
  (Polychromatic418967fa.accept_7_1_4_5_1_35 29 53 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 173 (accept_3_2 28 53 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 173 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 53 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 173 (Polychromatic418967fa.accept_16_10_5_13_1_8591 26 53 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 173 (accept_3_2 25 53 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 173 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 53 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 173
  (Polychromatic418967fa.accept_7_2_4_5_1_313 23 53 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 173 (accept_3_2 22 53 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 173 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 53 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 173 (Polychromatic418967fa.accept_7_6_4_5_1_314 20 53 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 173 (accept_3_2 19 53 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 173 (Polychromatic418967fa.accept_13_5_1_4_1_3966 18 53 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 173
  (Polychromatic418967fa.accept_16_1_5_13_1_1025 17 53 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 173 (accept_3_2 16 53 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 173 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 53 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 173 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 53 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 173 (accept_3_2 13 53 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 173 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 53 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 173
  (Polychromatic418967fa.accept_17_11_2_3_1_8468 11 53 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 173 (accept_3_2 10 53 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 173 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 53 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 173 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 53 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 173 (accept_3_2 7 53 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 173 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 53 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 173
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 53 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 173 (accept_3_2 4 53 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  173 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 53 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 173 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 53 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 173 (accept_3_2 1 53 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 173))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 173 (allA_of_3_0 52 52
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 173 (allA_succ_of_accept 50 51 173
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 51 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 173 (accept_3_2 49 51 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  51 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 51 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 51 173 (Polychromatic418967fa.accept_13_8_12_4_1_4858 47 51 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 173 (accept_3_2 46 51 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 173 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 51 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 51 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 173 (accept_3_2 43 51 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  51 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 51 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 51 173 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 51 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 173 (accept_3_2 40 51 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 173 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 51 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 173
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 51 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 173 (accept_3_2 37 51 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  51 173 (Polychromatic418967fa.accept_21_15_9_5_1_6588 36 51 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 51 173 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 51 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 173 (accept_3_2 34 51 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 173 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 51 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 51 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 173 (accept_3_2 31 51 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  51 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 51 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 51 173 (Polychromatic418967fa.accept_13_3_12_4_1_110 29 51 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 173 (accept_3_2 28 51 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 173 (Polychromatic418967fa.accept_18_9_15_11_1_5693 27 51 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 173
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 51 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 173 (accept_3_2 25 51 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  51 173 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 51 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 51 173 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 51 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 173 (accept_3_2 22 51 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 51 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 51 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 173 (accept_3_2 19 51 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  51 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 51 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 51 173 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 51 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 173 (accept_3_2 16 51 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 173 (Polychromatic418967fa.accept_11_4_7_8_1_1926 15 51 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 173
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 51 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 173 (accept_3_2 13 51 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  51 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 51 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 51 173 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 51 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 173 (accept_3_2 10 51 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 173 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 51 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 51 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 173 (accept_3_2 7 51 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51
  173 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 51 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 173 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 51 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 173 (accept_3_2 4 51 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 51 173 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 51 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 51
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 173 (accept_3_2 1 51 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 173)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 173 (allA_succ_of_accept 49 50 173 (accept_3_2 49 50 173 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 50 173 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 50 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 50 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 50 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 173 (accept_3_2 46 50 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 50 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 45
  50 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 50 173
  (Polychromatic418967fa.accept_9_8_5_2_1_422 44 50 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 50 173 (accept_3_2 43 50 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  50 173 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 50 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 50 173 (Polychromatic418967fa.accept_7_6_1_5_1_322 41 50 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 50 173 (accept_3_2 40 50 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 50 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 50 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 173
  (Polychromatic418967fa.accept_7_3_1_5_1_44 38 50 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 50 173 (accept_3_2 37 50 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  50 173 (Polychromatic418967fa.accept_11_3_6_8_1_1924 36 50 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 50 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 50 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 50 173 (accept_3_2 34 50 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 50 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 50 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 50 173
  (Polychromatic418967fa.accept_7_4_1_5_1_540 32 50 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 50 173 (accept_3_2 31 50 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  50 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 50 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 50 173 (Polychromatic418967fa.accept_15_14_5_8_1_3175 29 50 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 173 (accept_3_2 28 50 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 50 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 50 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 173
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 50 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 50 173 (accept_3_2 25 50 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  50 173 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 50 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 50 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 50 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 173 (accept_3_2 22 50 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 50 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 50 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 50 173
  (Polychromatic418967fa.accept_7_6_1_5_1_322 20 50 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 50 173 (accept_3_2 19 50 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  50 173 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 50 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 50 173 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 50 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 173 (accept_3_2 16 50 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 50 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 50 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 50 173
  (Polychromatic418967fa.accept_11_3_6_8_1_1924 14 50 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 50 173 (accept_3_2 13 50 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  50 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 50 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 50 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 50 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 50 173 (accept_3_2 10 50 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 50 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 50 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 173
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 50 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 50 173 (accept_3_2 7 50 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50
  173 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 50 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 50 173 (Polychromatic418967fa.accept_16_5_2_13_1_1007 5 50 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 50 173 (accept_3_2 4 50 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 50 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 50 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 173 (Polychromatic418967fa.accept_13_2_11_4_1_445 2
  50 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 50 173 (accept_3_2 1 50 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 173)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  49 173 (allA_of_3_0 49 49 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 48 173 (allA_succ_of_accept 47 48
  173 (Polychromatic418967fa.accept_13_8_9_4_1_1552 47 48 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 48 173 (accept_3_2 46 48 173 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 48 173 (Polychromatic418967fa.accept_10_5_8_3_1_229 45 48 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 48 173 (Polychromatic418967fa.accept_9_8_3_2_1_417 44 48 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 173 (accept_3_2 43 48 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 48 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 42
  48 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 48 173
  (Polychromatic418967fa.accept_9_5_3_2_1_171 41 48 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 48 173 (accept_3_2 40 48 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  48 173 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 48 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 48 173 (Polychromatic418967fa.accept_20_18_8_13_1_6761 38 48 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 173 (accept_3_2 37 48 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 173 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 48 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 48 173
  (Polychromatic418967fa.accept_9_8_3_2_1_417 35 48 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 48 173 (accept_3_2 34 48 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  48 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 48 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 48 173 (Polychromatic418967fa.accept_7_4_6_5_1_141 32 48 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 173 (accept_3_2 31 48 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 173 (Polychromatic418967fa.accept_19_11_10_2_1_9757 30 48 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 48 173
  (Polychromatic418967fa.accept_7_1_6_5_1_39 29 48 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 48 173 (accept_3_2 28 48 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  48 173 (Polychromatic418967fa.accept_14_13_6_5_1_1853 27 48 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 48 173 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 48 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 173 (accept_3_2 25 48 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 48 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 48 173
  (Polychromatic418967fa.accept_9_5_3_2_1_171 23 48 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 48 173 (accept_3_2 22 48 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  48 173 (Polychromatic418967fa.accept_10_1_8_3_1_947 21 48 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 48 173 (Polychromatic418967fa.accept_13_7_9_4_1_918 20 48 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 173 (accept_3_2 19 48 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 48 173 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 48 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 48 173
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 48 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 48 173 (accept_3_2 16 48 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  48 173 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 48 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 48 173 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 48 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 173 (accept_3_2 13 48 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 48 173 (Polychromatic418967fa.accept_11_1_4_8_1_1918 12 48 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 48 173
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 48 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 48 173 (accept_3_2 10 48 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  48 173 (Polychromatic418967fa.accept_15_9_3_8_1_3155 9 48 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 48 173 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 48 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 173 (accept_3_2 7 48 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 48 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 48 173
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 48 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 48 173 (accept_3_2 4 48 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 48
  173 (Polychromatic418967fa.accept_20_3_8_13_1_3832 3 48 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 48 173 (Polychromatic418967fa.accept_17_2_14_3_1_4679 2 48 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 173 (accept_3_2 1 48 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 48 173)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 173
  (allA_succ_of_accept 46 47 173 (accept_3_2 46 47 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  47 173 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 47 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 47 173 (Polychromatic418967fa.accept_10_4_7_3_1_54 44 47 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 173 (accept_3_2 43 47 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 47 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 47 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 173
  (Polychromatic418967fa.accept_24_17_23_5_1_9756 41 47 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 47 173 (accept_3_2 40 47 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  47 173 (Polychromatic418967fa.accept_11_6_3_8_1_843 39 47 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 47 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 47 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 173 (accept_3_2 37 47 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 47 173 (Polychromatic418967fa.accept_10_6_7_3_1_547 36 47 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 173
  (Polychromatic418967fa.accept_10_5_7_3_1_561 35 47 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 173 (accept_3_2 34 47 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 173 (Polychromatic418967fa.accept_17_16_13_3_1_4677 33 47 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 173 (Polychromatic418967fa.accept_23_9_1_12_1_9755 32 47 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 173 (accept_3_2 31 47 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 47 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 173
  (Polychromatic418967fa.accept_22_7_3_19_1_8158 29 47 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 173 (accept_3_2 28 47 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 173 (Polychromatic418967fa.accept_11_5_3_8_1_454 27 47 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 47 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 173 (accept_3_2 25 47 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 173 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 47 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 173
  (Polychromatic418967fa.accept_13_10_8_4_1_3098 23 47 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 173 (accept_3_2 22 47 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 173 (Polychromatic418967fa.accept_15_6_2_8_1_2223 21 47 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 173 (Polychromatic418967fa.accept_19_1_9_2_1_6945 20 47 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 173 (accept_3_2 19 47 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 47 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 173
  (Polychromatic418967fa.accept_11_6_3_8_1_843 17 47 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 173 (accept_3_2 16 47 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 173 (Polychromatic418967fa.accept_10_5_7_3_1_561 15 47 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 47 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 173 (accept_3_2 13 47 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 173 (Polychromatic418967fa.accept_13_12_8_4_1_3099 12 47 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 173
  (Polychromatic418967fa.accept_13_11_8_4_1_3950 11 47 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 173 (accept_3_2 10 47 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 173 (Polychromatic418967fa.accept_13_9_8_4_1_937 9 47 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 173 (Polychromatic418967fa.accept_17_8_13_3_1_3432 8 47 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 173 (accept_3_2 7 47 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 47 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 173
  (Polychromatic418967fa.accept_10_5_7_3_1_561 5 47 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 173 (accept_3_2 4 47 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  173 (Polychromatic418967fa.accept_16_3_15_13_1_2825 3 47 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 47 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 47 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 173 (accept_3_2 1 47 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 47 173))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 173 (allA_of_3_0 46
  46 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 45 173 (allA_succ_of_accept 44 45 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 45 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 173 (accept_3_2 43 45 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  45 173 (Polychromatic418967fa.accept_10_2_5_3_1_1408 42 45 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 45 173 (Polychromatic418967fa.accept_13_2_6_4_1_1593 41 45 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 173 (accept_3_2 40 45 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 173 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 45 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 45 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 173 (accept_3_2 37 45 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  45 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 45 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 45 173 (Polychromatic418967fa.accept_13_9_6_4_1_2243 35 45 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 173 (accept_3_2 34 45 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 173 (Polychromatic418967fa.accept_13_7_6_4_1_933 33 45 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 45 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 173 (accept_3_2 31 45 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  45 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 45 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 45 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 45 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 173 (accept_3_2 28 45 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 173 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 45 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 45 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 173 (accept_3_2 25 45 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  45 173 (Polychromatic418967fa.accept_13_11_6_4_1_3121 24 45 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 45 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 45 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 173 (accept_3_2 22 45 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 173 (Polychromatic418967fa.accept_25_21_20_23_1_9754 21 45 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 45 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 45 173 (accept_3_2 19 45 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  45 173 (Polychromatic418967fa.accept_10_8_5_3_1_543 18 45 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 45 173 (Polychromatic418967fa.accept_10_7_5_3_1_542 17 45 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 173 (accept_3_2 16 45 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 45 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 45 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 173 (accept_3_2 13 45 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  45 173 (Polychromatic418967fa.accept_10_2_5_3_1_1408 12 45 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 45 173 (Polychromatic418967fa.accept_13_11_6_4_1_3121 11 45 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 173 (accept_3_2 10 45 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 45 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 45 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 173 (accept_3_2 7 45 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45
  173 (Polychromatic418967fa.accept_21_6_3_5_1_8198 6 45 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 45 173 (Polychromatic418967fa.accept_13_5_6_4_1_1582 5 45 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 173 (accept_3_2 4 45 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 45 173 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 45 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 45 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 45 173 (accept_3_2 1 45 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  173))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 173 (allA_succ_of_accept 43 44 173 (accept_3_2 43 44
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 44 173
  (Polychromatic418967fa.accept_9_6_8_2_1_410 42 44 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 44 173 (Polychromatic418967fa.accept_8_1_4_5_1_48 41 44 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 173 (accept_3_2 40 44 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 44 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 44 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 173 (Polychromatic418967fa.accept_7_3_2_5_1_147 38
  44 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 44 173 (accept_3_2 37 44
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 44 173
  (Polychromatic418967fa.accept_13_10_5_4_1_3107 36 44 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 44 173 (Polychromatic418967fa.accept_13_9_5_4_1_1591 35 44 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 173 (accept_3_2 34 44 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 44 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 44 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 44 173 (Polychromatic418967fa.accept_7_4_2_5_1_527 32
  44 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 44 173 (accept_3_2 31 44
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 44 173
  (Polychromatic418967fa.accept_9_3_8_2_1_162 30 44 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 44 173 (Polychromatic418967fa.accept_10_9_4_3_1_539 29 44 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 44 173 (accept_3_2 28 44 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 44 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 44 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 44 173 (Polychromatic418967fa.accept_12_2_8_5_1_408
  26 44 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 44 173 (accept_3_2 25
  44 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 44 173
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 44 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 44 173 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 44 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 44 173 (accept_3_2 22 44 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 44 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 44 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 44 173 (Polychromatic418967fa.accept_15_5_14_8_1_1376
  20 44 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 44 173 (accept_3_2 19
  44 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 44 173
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 44 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 44 173 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 44 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 44 173 (accept_3_2 16 44 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 44 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 44 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 44 173 (Polychromatic418967fa.accept_9_5_8_2_1_409 14
  44 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 44 173 (accept_3_2 13 44
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 44 173
  (Polychromatic418967fa.accept_9_3_8_2_1_162 12 44 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 44 173 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 44 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 44 173 (accept_3_2 10 44 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 44 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 44 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 44 173 (Polychromatic418967fa.accept_16_8_12_13_1_3851
  8 44 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 44 173 (accept_3_2 7 44
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 44 173 (Polychromatic418967fa.accept_9_6_8_2_1_410
  6 44 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 44 173
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 44 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 44 173 (accept_3_2 4 44 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 44
  173 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 44 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 44 173 (Polychromatic418967fa.accept_12_2_8_5_1_408 2 44 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 173 (accept_3_2 1 44 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 44 173)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 173 (allA_of_3_0 43 43 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 173 (allA_succ_of_accept 41 42 173
  (Polychromatic418967fa.accept_9_5_6_2_1_161 41 42 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 42 173 (accept_3_2 40 42 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  42 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 42 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 42 173 (Polychromatic418967fa.accept_13_12_3_4_1_928 38 42 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 173 (accept_3_2 37 42 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 173 (Polychromatic418967fa.accept_19_17_4_2_1_8360 36 42 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 42 173
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 42 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 42 173 (accept_3_2 34 42 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  42 173 (Polychromatic418967fa.accept_13_7_3_4_1_459 33 42 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 42 173 (Polychromatic418967fa.accept_9_5_6_2_1_161 32 42 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 173 (accept_3_2 31 42 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 42 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 42 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 42 173
  (Polychromatic418967fa.accept_17_12_8_3_1_4646 29 42 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 42 173 (accept_3_2 28 42 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  42 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 42 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 42 173 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 42 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 173 (accept_3_2 25 42 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 173 (Polychromatic418967fa.accept_19_5_4_2_1_6840 24 42 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 42 173
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 42 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 42 173 (accept_3_2 22 42 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  42 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 42 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 42 173 (Polychromatic418967fa.accept_13_7_3_4_1_459 20 42 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 173 (accept_3_2 19 42 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 42 173 (Polychromatic418967fa.accept_15_3_12_8_1_738 18 42 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 42 173
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 42 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 42 173 (accept_3_2 16 42 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  42 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 42 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 42 173 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 42 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 173 (accept_3_2 13 42 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 42 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 42 173
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 42 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 42 173 (accept_3_2 10 42 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  42 173 (Polychromatic418967fa.accept_19_9_4_2_1_9753 9 42 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 42 173 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 42 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 173 (accept_3_2 7 42 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 42 173 (Polychromatic418967fa.accept_19_6_4_2_1_1726 6 42 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 42 173
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 42 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 42 173 (accept_3_2 4 42 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 42
  173 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 42 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 42 173 (Polychromatic418967fa.accept_22_2_20_19_1_9752 2 42 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 173 (accept_3_2 1 42 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 42 173)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 173 (allA_succ_of_accept 40 41
  173 (accept_3_2 40 41 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 173
  (Polychromatic418967fa.accept_7_4_6_5_1_141 39 41 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 173 (Polychromatic418967fa.accept_10_8_1_3_1_1374 38 41 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 173 (accept_3_2 37 41 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 173 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 41 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 173 (Polychromatic418967fa.accept_9_8_5_2_1_422 35
  41 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 173 (accept_3_2 34 41
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 173
  (Polychromatic418967fa.accept_9_6_5_2_1_421 33 41 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 41 173 (Polychromatic418967fa.accept_7_4_6_5_1_141 32 41 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 173 (accept_3_2 31 41 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 41 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 41 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 173 (Polychromatic418967fa.accept_7_1_6_5_1_39 29
  41 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 173 (accept_3_2 28 41
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 41 173
  (Polychromatic418967fa.accept_15_12_11_8_1_1392 27 41 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 41 173 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 41 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 173 (accept_3_2 25 41 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 41 173 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 41 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 173 (Polychromatic418967fa.accept_16_7_9_13_1_4948
  23 41 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 173 (accept_3_2 22
  41 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 41 173
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 41 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 41 173 (Polychromatic418967fa.accept_8_4_1_5_1_186 20 41 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 173 (accept_3_2 19 41 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 41 173 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 41 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 173 (Polychromatic418967fa.accept_9_8_5_2_1_422 17
  41 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 173 (accept_3_2 16 41
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 173 (Polychromatic418967fa.accept_7_1_6_5_1_39
  15 41 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 173
  (Polychromatic418967fa.accept_18_14_5_11_1_5676 14 41 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 41 173 (accept_3_2 13 41 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  41 173 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 41 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 41 173 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 41 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 173 (accept_3_2 10 41 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 41 173 (Polychromatic418967fa.accept_23_9_18_12_1_9751 9 41 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 173
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 41 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 41 173 (accept_3_2 7 41 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41
  173 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 41 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 41 173 (Polychromatic418967fa.accept_13_5_2_4_1_3955 5 41 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 173 (accept_3_2 4 41 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 41 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 41 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 173 (Polychromatic418967fa.accept_10_2_1_3_1_233 2
  41 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 173 (accept_3_2 1 41 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41 173))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 173
  (allA_of_3_0 40 40 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 173 (allA_succ_of_accept 38 39 173
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 39 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 173 (accept_3_2 37 39 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 173 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 39 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 173 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 39 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 173 (accept_3_2 34 39 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 39 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 39 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 173 (accept_3_2 31 39 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 39 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 173 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 39 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 173 (accept_3_2 28 39 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 173 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 39 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 173
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 39 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 173 (accept_3_2 25 39 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 39 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 173 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 39 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 173 (accept_3_2 22 39 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 173 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 39 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 39 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 173 (accept_3_2 19 39 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 39 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 173 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 39 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 173 (accept_3_2 16 39 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 173 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 39 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 173
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 39 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 173 (accept_3_2 13 39 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  39 173 (Polychromatic418967fa.accept_19_12_1_2_1_9750 12 39 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 173 (Polychromatic418967fa.accept_21_11_18_5_1_8162 11 39 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 173 (accept_3_2 10 39 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 173 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 39 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 39 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 173 (accept_3_2 7 39 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  173 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 39 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 173 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 39 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 173 (accept_3_2 4 39 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 173 (Polychromatic418967fa.accept_11_3_6_8_1_1924 3 39 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 39
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 173 (accept_3_2 1 39 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 173))))))))))))))))))))))))))))))))))))))) (allB_succ 38 173
  (allA_succ_of_accept 37 38 173 (accept_3_2 37 38 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  38 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 38 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 38 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 38 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 173 (accept_3_2 34 38 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 38 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 173
  (Polychromatic418967fa.accept_12_8_2_5_1_844 32 38 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 38 173 (accept_3_2 31 38 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  38 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 38 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 38 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 38 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 173 (accept_3_2 28 38 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 38 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 38 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 173
  (Polychromatic418967fa.accept_10_6_8_3_1_930 26 38 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 38 173 (accept_3_2 25 38 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  38 173 (Polychromatic418967fa.accept_11_2_5_8_1_470 24 38 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 38 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 38 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 173 (accept_3_2 22 38 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 38 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 173
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 38 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 38 173 (accept_3_2 19 38 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  38 173 (Polychromatic418967fa.accept_13_5_12_4_1_449 18 38 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 38 173 (Polychromatic418967fa.accept_18_17_2_11_1_9749 17 38 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 173 (accept_3_2 16 38 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 38 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 173
  (Polychromatic418967fa.accept_11_3_5_8_1_458 14 38 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 38 173 (accept_3_2 13 38 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  38 173 (Polychromatic418967fa.accept_14_12_10_5_1_2712 12 38 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 38 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 38 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 173 (accept_3_2 10 38 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 38 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 173
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 38 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 173 (accept_3_2 7 38 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  173 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 38 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 38 173 (Polychromatic418967fa.accept_10_5_8_3_1_229 5 38 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 173 (accept_3_2 4 38 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 38 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 38 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 38
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 173 (accept_3_2 1 38 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 173)))))))))))))))))))))))))))))))))))))) (allB_succ 37 173
  (allA_of_3_0 37 37 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 36 173 (allA_succ_of_accept 35 36 173
  (Polychromatic418967fa.accept_17_1_2_3_1_4668 35 36 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 36 173 (accept_3_2 34 36 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  36 173 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 36 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 36 173 (Polychromatic418967fa.accept_7_4_1_5_1_540 32 36 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 173 (accept_3_2 31 36 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 36 173 (Polychromatic418967fa.accept_21_9_15_5_1_3500 30 36 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 36 173
  (Polychromatic418967fa.accept_10_9_6_3_1_545 29 36 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 36 173 (accept_3_2 28 36 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  36 173 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 36 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 36 173 (Polychromatic418967fa.accept_19_7_17_2_1_6855 26 36 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 173 (accept_3_2 25 36 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 36 173 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 36 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 36 173
  (Polychromatic418967fa.accept_16_7_4_13_1_1057 23 36 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 36 173 (accept_3_2 22 36 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  36 173 (Polychromatic418967fa.accept_13_8_10_4_1_2270 21 36 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 36 173 (Polychromatic418967fa.accept_7_6_1_5_1_322 20 36 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 173 (accept_3_2 19 36 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 173 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 36 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 36 173
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 36 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 36 173 (accept_3_2 16 36 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  36 173 (Polychromatic418967fa.accept_19_15_17_2_1_4097 15 36 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 36 173 (Polychromatic418967fa.accept_13_1_10_4_1_954 14 36 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 173 (accept_3_2 13 36 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 36 173 (Polychromatic418967fa.accept_16_12_4_13_1_3827 12 36 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 36 173
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 36 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 36 173 (accept_3_2 10 36 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  36 173 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 36 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 36 173 (Polychromatic418967fa.accept_10_8_6_3_1_1394 8 36 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 173 (accept_3_2 7 36 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 36 173 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 36 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 36 173
  (Polychromatic418967fa.accept_11_5_3_8_1_454 5 36 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 36 173 (accept_3_2 4 36 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 36
  173 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 36 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 36 173 (Polychromatic418967fa.accept_15_2_6_8_1_754 2 36 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 173 (accept_3_2 1 36 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 36 173)))))))))))))))))))))))))))))))))))) (allB_succ 35 173 (allA_succ_of_accept 34 35 173
  (accept_3_2 34 35 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 173
  (Polychromatic418967fa.accept_9_6_8_2_1_410 33 35 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 173 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 35 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 173 (accept_3_2 31 35 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 35 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 35 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 173 (Polychromatic418967fa.accept_15_14_5_8_1_3175
  29 35 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 173 (accept_3_2 28
  35 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 173
  (Polychromatic418967fa.accept_10_7_5_3_1_542 27 35 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 35 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 35 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 173 (accept_3_2 25 35 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 35 173 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 35 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 173 (Polychromatic418967fa.accept_9_5_8_2_1_409 23
  35 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 173 (accept_3_2 22 35
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 173
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 35 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 35 173 (Polychromatic418967fa.accept_13_7_9_4_1_918 20 35 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 35 173 (accept_3_2 19 35 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 35 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 35 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 173 (Polychromatic418967fa.accept_10_7_5_3_1_542
  17 35 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 173 (accept_3_2 16
  35 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 173
  (Polychromatic418967fa.accept_9_6_8_2_1_410 15 35 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 35 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 35 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 173 (accept_3_2 13 35 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 35 173 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 35 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 173 (Polychromatic418967fa.accept_15_11_5_8_1_3157
  11 35 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 173 (accept_3_2 10
  35 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 35 173
  (Polychromatic418967fa.accept_14_9_7_5_1_1105 9 35 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 35 173 (Polychromatic418967fa.accept_10_8_5_3_1_543 8 35 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 173 (accept_3_2 7 35 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 35 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 35 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 173 (Polychromatic418967fa.accept_9_5_8_2_1_409 5
  35 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 173 (accept_3_2 4 35 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 173 (Polychromatic418967fa.accept_9_3_8_2_1_162 3
  35 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 173
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 35 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 35 173 (accept_3_2 1 35 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35
  173))))))))))))))))))))))))))))))))))) (allB_succ 34 173 (allA_of_3_0 34 34 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 33 173 (allA_succ_of_accept 32 33 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 33 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 173 (accept_3_2 31 33 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 30
  33 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 173
  (Polychromatic418967fa.accept_13_3_7_4_1_435 29 33 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 33 173 (accept_3_2 28 33 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  33 173 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 33 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 33 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 33 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 173 (accept_3_2 25 33 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 33 173 (Polychromatic418967fa.accept_13_11_7_4_1_1561 24 33 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 173
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 33 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 33 173 (accept_3_2 22 33 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  33 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 33 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 33 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 33 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 173 (accept_3_2 19 33 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 173 (Polychromatic418967fa.accept_21_18_12_5_1_6592 18 33 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 173
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 33 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 173 (accept_3_2 16 33 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  33 173 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 33 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 33 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 33 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 173 (accept_3_2 13 33 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 173 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 33 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 173
  (Polychromatic418967fa.accept_13_11_7_4_1_1561 11 33 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 33 173 (accept_3_2 10 33 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  33 173 (Polychromatic418967fa.accept_13_9_7_4_1_953 9 33 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 33 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 33 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 173 (accept_3_2 7 33 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 173 (Polychromatic418967fa.accept_13_6_7_4_1_2264 6 33 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 173
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 33 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 33 173 (accept_3_2 4 33 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33
  173 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 33 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 33 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 33 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 173 (accept_3_2 1 33 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 33 173))))))))))))))))))))))))))))))))) (allB_succ 32 173 (allA_succ_of_accept 31 32 173
  (accept_3_2 31 32 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 32 173
  (Polychromatic418967fa.accept_7_2_4_5_1_313 30 32 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 32 173 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 32 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 173 (accept_3_2 28 32 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 32 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 32 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 173 (Polychromatic418967fa.accept_9_8_5_2_1_422 26
  32 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 32 173 (accept_3_2 25 32
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 32 173
  (Polychromatic418967fa.accept_9_6_5_2_1_421 24 32 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 32 173 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 32 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 173 (accept_3_2 22 32 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 32 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 32 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 173 (Polychromatic418967fa.accept_7_6_4_5_1_314 20
  32 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 32 173 (accept_3_2 19 32
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 32 173
  (Polychromatic418967fa.accept_13_5_6_4_1_1582 18 32 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 32 173 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 32 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 32 173 (accept_3_2 16 32 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 32 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 32 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 32 173 (Polychromatic418967fa.accept_12_2_8_5_1_408
  14 32 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 32 173 (accept_3_2 13
  32 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 32 173
  (Polychromatic418967fa.accept_9_3_5_2_1_28 12 32 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 32 173 (Polychromatic418967fa.accept_10_1_2_3_1_1910 11 32 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 173 (accept_3_2 10 32 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 32 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 32 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 173 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 32
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 32 173 (accept_3_2 7 32 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32 173 (Polychromatic418967fa.accept_7_6_4_5_1_314 6
  32 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 32 173
  (Polychromatic418967fa.accept_10_5_2_3_1_239 5 32 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 32 173 (accept_3_2 4 32 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 32
  173 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 32 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 32 173 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 32 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 173 (accept_3_2 1 32 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 32 173)))))))))))))))))))))))))))))))) (allB_succ 31 173 (allA_of_3_0 31 31 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 30 173 (allA_succ_of_accept 29 30 173
  (Polychromatic418967fa.accept_19_10_11_2_1_8354 29 30 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 30 173 (accept_3_2 28 30 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  30 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 30 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 30 173 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 30 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 30 173 (accept_3_2 25 30 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 30 173 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 30 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 30 173
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 30 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 30 173 (accept_3_2 22 30 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  30 173 (Polychromatic418967fa.accept_14_7_2_5_1_4528 21 30 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 30 173 (Polychromatic418967fa.accept_22_20_8_19_1_9748 20 30 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 173 (accept_3_2 19 30 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 173 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 30 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 30 173
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 30 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 30 173 (accept_3_2 16 30 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  30 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 30 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 30 173 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 30 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 173 (accept_3_2 13 30 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 173 (Polychromatic418967fa.accept_20_12_10_13_1_9747 12 30 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 30 173
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 30 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 30 173 (accept_3_2 10 30 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  30 173 (Polychromatic418967fa.accept_18_9_12_11_1_5642 9 30 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 30 173 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 30 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 173 (accept_3_2 7 30 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 30 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 30 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 30 173
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 30 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 30 173 (accept_3_2 4 30 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 30
  173 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 30 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 30 173 (Polychromatic418967fa.accept_20_2_10_13_1_6766 2 30 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 173 (accept_3_2 1 30 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 30 173)))))))))))))))))))))))))))))) (allB_succ 29 173 (allA_succ_of_accept 28 29 173
  (accept_3_2 28 29 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 173
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 29 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 173 (Polychromatic418967fa.accept_10_6_9_3_1_935 26 29 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 173 (accept_3_2 25 29 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 173 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 29 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 173 (Polychromatic418967fa.accept_21_2_8_5_1_5057
  23 29 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 173 (accept_3_2 22
  29 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 173
  (Polychromatic418967fa.accept_15_6_14_8_1_245 21 29 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 29 173 (Polychromatic418967fa.accept_7_6_1_5_1_322 20 29 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 173 (accept_3_2 19 29 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 29 173 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 29 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 173 (Polychromatic418967fa.accept_7_3_1_5_1_44 17
  29 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 173 (accept_3_2 16 29
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 173
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 15 29 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 29 173 (Polychromatic418967fa.accept_10_4_9_3_1_1907 14 29 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 173 (accept_3_2 13 29 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 29 173 (Polychromatic418967fa.accept_13_12_3_4_1_928 12 29 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 173 (Polychromatic418967fa.accept_7_4_1_5_1_540 11
  29 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 173 (accept_3_2 10 29
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 29 173
  (Polychromatic418967fa.accept_15_9_14_8_1_1396 9 29 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 29 173 (Polychromatic418967fa.accept_17_8_12_3_1_5927 8 29 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 173 (accept_3_2 7 29 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 29 173 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 29 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 173 (Polychromatic418967fa.accept_15_5_14_8_1_1376
  5 29 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 173 (accept_3_2 4 29
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29 173 (Polychromatic418967fa.accept_7_3_1_5_1_44
  3 29 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 173
  (Polychromatic418967fa.accept_20_2_9_13_1_2599 2 29 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 29 173 (accept_3_2 1 29 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29
  173))))))))))))))))))))))))))))) (allB_succ 28 173 (allA_of_3_0 28 28 173 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 27 173 (allA_succ_of_accept 26 27 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 27 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 173 (accept_3_2 25 27 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 173 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 27 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 173
  (Polychromatic418967fa.accept_13_10_1_4_1_3103 23 27 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 27 173 (accept_3_2 22 27 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  27 173 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 27 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 27 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 27 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 173 (accept_3_2 19 27 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 27 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 27 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 173
  (Polychromatic418967fa.accept_22_17_5_19_1_9746 17 27 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 27 173 (accept_3_2 16 27 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  27 173 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 27 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 27 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 27 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 173 (accept_3_2 13 27 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 27 173 (Polychromatic418967fa.accept_18_12_9_11_1_4370 12 27 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 173
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 27 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 27 173 (accept_3_2 10 27 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  27 173 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 27 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 27 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 27 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 173 (accept_3_2 7 27 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 27 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 27 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 173
  (Polychromatic418967fa.accept_10_5_7_3_1_561 5 27 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 27 173 (accept_3_2 4 27 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27
  173 (Polychromatic418967fa.accept_11_3_5_8_1_458 3 27 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 27 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 27 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 173 (accept_3_2 1 27 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 27 173))))))))))))))))))))))))))) (allB_succ 26 173 (allA_succ_of_accept 25 26 173 (accept_3_2
  25 26 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 26 173
  (Polychromatic418967fa.accept_9_6_8_2_1_410 24 26 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 26 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 26 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 26 173 (accept_3_2 22 26 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 26 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 26 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 26 173 (Polychromatic418967fa.accept_12_8_2_5_1_844
  20 26 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 26 173 (accept_3_2 19
  26 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 26 173
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 26 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 26 173 (Polychromatic418967fa.accept_10_7_6_3_1_927 17 26 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 26 173 (accept_3_2 16 26 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 26 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 26 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 26 173 (Polychromatic418967fa.accept_9_5_8_2_1_409 14
  26 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 26 173 (accept_3_2 13 26
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 26 173
  (Polychromatic418967fa.accept_9_3_8_2_1_162 12 26 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 26 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 26 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 26 173 (accept_3_2 10 26 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 26 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 26 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 26 173 (Polychromatic418967fa.accept_10_8_6_3_1_1394 8
  26 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 26 173 (accept_3_2 7 26 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 26 173 (Polychromatic418967fa.accept_9_6_8_2_1_410 6
  26 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 26 173
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 26 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 26 173 (accept_3_2 4 26 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 26
  173 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 26 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 26 173 (Polychromatic418967fa.accept_27_2_26_11_1_9745 2 26 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 26 173 (accept_3_2 1 26 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 26 173)))))))))))))))))))))))))) (allB_succ 25 173 (allA_of_3_0 25 25 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 24 173 (allA_succ_of_accept 23 24 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 24
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 173 (accept_3_2 22 24 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 24 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 21
  24 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 24 173
  (Polychromatic418967fa.accept_13_7_11_4_1_2247 20 24 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 24 173 (accept_3_2 19 24 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  24 173 (Polychromatic418967fa.accept_15_3_9_8_1_3164 18 24 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 24 173 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 24 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 173 (accept_3_2 16 24 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 24 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 24 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 24 173
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 24 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 24 173 (accept_3_2 13 24 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  24 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 24 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 24 173 (Polychromatic418967fa.accept_16_11_8_13_1_3844 11 24 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 24 173 (accept_3_2 10 24 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 24 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 24 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 24 173
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 24 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 24 173 (accept_3_2 7 24 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 24
  173 (Polychromatic418967fa.accept_13_6_11_4_1_938 6 24 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 24 173 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 24 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24 173 (accept_3_2 4 24 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 24 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 24 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 24 173
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 24 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 24 173 (accept_3_2 1 24 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24
  173)))))))))))))))))))))))) (allB_succ 23 173 (allA_succ_of_accept 22 23 173 (accept_3_2 22 23 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 23 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 23 173
  (Polychromatic418967fa.accept_13_7_10_4_1_919 20 23 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 23 173 (accept_3_2 19 23 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  23 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 23 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 23 173 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 23 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 173 (accept_3_2 16 23 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 173 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 23 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 173
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 23 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 173 (accept_3_2 13 23 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  23 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 23 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 23 173 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 23 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 173 (accept_3_2 10 23 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 173 (Polychromatic418967fa.accept_16_9_7_13_1_4997 9 23 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 173
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 23 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 23 173 (accept_3_2 7 23 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23
  173 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 23 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 23 173 (Polychromatic418967fa.accept_13_5_10_4_1_1564 5 23 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 173 (accept_3_2 4 23 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 23 173 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 23 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 23
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 173 (accept_3_2 1 23 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23 173))))))))))))))))))))))) (allB_succ 22 173 (allA_of_3_0 22 22
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 21 173 (allA_succ_of_accept 20 21 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 21 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 173 (accept_3_2 19 21 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  21 173 (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 21 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 21 173 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 21 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 173 (accept_3_2 16 21 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 173 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 21 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 21 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 21 173 (accept_3_2 13 21 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  21 173 (Polychromatic418967fa.accept_10_2_1_3_1_233 12 21 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 21 173 (Polychromatic418967fa.accept_13_11_8_4_1_3950 11 21 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 173 (accept_3_2 10 21 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 173 (Polychromatic418967fa.accept_11_9_10_8_1_444 9 21 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 173
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 21 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 173 (accept_3_2 7 21 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21
  173 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 21 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 173 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 21 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 173 (accept_3_2 4 21 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 21 173 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 21 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 21
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 173 (accept_3_2 1 21 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 173))))))))))))))))))))) (allB_succ 20 173 (allA_succ_of_accept
  19 20 173 (accept_3_2 19 20 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 20 173
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 20 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 20 173 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 20 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 173 (accept_3_2 16 20 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 20 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 20 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 20 173 (Polychromatic418967fa.accept_12_2_8_5_1_408
  14 20 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 20 173 (accept_3_2 13
  20 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 20 173
  (Polychromatic418967fa.accept_13_12_7_4_1_3124 12 20 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 20 173 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 20 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 20 173 (accept_3_2 10 20 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 20 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 20 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 173 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 20
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 20 173 (accept_3_2 7 20 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20 173 (Polychromatic418967fa.accept_13_6_7_4_1_2264 6
  20 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 20 173
  (Polychromatic418967fa.accept_25_5_20_23_1_9744 5 20 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 20 173 (accept_3_2 4 20 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 20
  173 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 20 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 20 173 (Polychromatic418967fa.accept_12_2_8_5_1_408 2 20 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 20 173 (accept_3_2 1 20 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 173)))))))))))))))))))) (allB_succ 19 173 (allA_of_3_0 19 19 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 18 173 (allA_succ_of_accept 17 18 173 (Polychromatic418967fa.accept_23_17_18_12_1_9743 17 18
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 173 (accept_3_2 16 18 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 18 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 15
  18 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 173
  (Polychromatic418967fa.accept_13_1_5_4_1_463 14 18 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 18 173 (accept_3_2 13 18 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  18 173 (Polychromatic418967fa.accept_13_12_5_4_1_3133 12 18 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 18 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 18 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 173 (accept_3_2 10 18 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 18 173 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 18 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 173
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 18 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 18 173 (accept_3_2 7 18 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18
  173 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 18 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 18 173 (Polychromatic418967fa.accept_10_5_8_3_1_229 5 18 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 173 (accept_3_2 4 18 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 18 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 18 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 18 173 (Polychromatic418967fa.accept_7_2_4_5_1_313 2
  18 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 173 (accept_3_2 1 18 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 173)))))))))))))))))) (allB_succ 17 173 (allA_succ_of_accept 16
  17 173 (accept_3_2 16 17 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 173
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 17 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 17 173 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 17 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 173 (accept_3_2 13 17 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 17 173 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 17 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 173
  (Polychromatic418967fa.accept_21_11_17_5_1_8161 11 17 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 17 173 (accept_3_2 10 17 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  17 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 17 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 17 173 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 17 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 173 (accept_3_2 7 17 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 17 173 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 17 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 173
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 17 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 17 173 (accept_3_2 4 17 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17
  173 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 17 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 17 173 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 17 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 173 (accept_3_2 1 17 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 17 173))))))))))))))))) (allB_succ 16 173 (allA_of_3_0 16 16 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 15 173 (allA_succ_of_accept 14 15 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 15 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 173 (accept_3_2 13 15 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 15 173 (Polychromatic418967fa.accept_9_3_6_2_1_160 12
  15 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 173
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 15 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 15 173 (accept_3_2 10 15 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  15 173 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 15 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 15 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 15 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 173 (accept_3_2 7 15 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 15 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 15 173
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 15 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 15 173 (accept_3_2 4 15 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 15
  173 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 15 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 15 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 15 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 173 (accept_3_2 1 15 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 15 173))))))))))))))) (allB_succ 14 173 (allA_succ_of_accept 13 14 173 (accept_3_2 13 14 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 14 173 (Polychromatic418967fa.accept_9_3_5_2_1_28 12
  14 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 14 173
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 14 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 14 173 (accept_3_2 10 14 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  14 173 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 14 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 14 173 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 14 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 14 173 (accept_3_2 7 14 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 14 173 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 14 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 14 173
  (Polychromatic418967fa.accept_11_5_3_8_1_454 5 14 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 14 173 (accept_3_2 4 14 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 14
  173 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 14 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 14 173 (Polychromatic418967fa.accept_17_2_14_3_1_4679 2 14 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 14 173 (accept_3_2 1 14 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 14 173)))))))))))))) (allB_succ 13 173 (allA_of_3_0 13 13 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 12 173 (allA_succ_of_accept 11 12 173 (Polychromatic418967fa.accept_10_1_2_3_1_1910 11 12 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 173 (accept_3_2 10 12 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 12 173 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 12
  173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 173
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 12 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 12 173 (accept_3_2 7 12 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12
  173 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 12 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 12 173 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 12 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 173 (accept_3_2 4 12 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 12 173 (Polychromatic418967fa.accept_13_3_12_4_1_110 3 12 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 12 173 (Polychromatic418967fa.accept_13_2_12_4_1_943 2
  12 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12 173 (accept_3_2 1 12 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 173)))))))))))) (allB_succ 11 173 (allA_succ_of_accept 10 11 173
  (accept_3_2 10 11 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 173
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 11 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 173 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 11 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 173 (accept_3_2 7 11 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 11 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 173 (Polychromatic418967fa.accept_15_5_11_8_1_1391
  5 11 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 173 (accept_3_2 4 11
  173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 173
  (Polychromatic418967fa.accept_15_3_11_8_1_4186 3 11 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 11 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 11 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 11 173 (accept_3_2 1 11 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 11 173))))))))))) (allB_succ 10 173 (allA_of_3_0 10 10 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 9 173 (allA_succ_of_accept 8 9 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 9 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 173 (accept_3_2 7 9 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 173 (Polychromatic418967fa.accept_10_6_9_3_1_935 6 9 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 173
  (Polychromatic418967fa.accept_13_5_9_4_1_441 5 9 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 9 173 (accept_3_2 4 9 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 173
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 9 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 9 173 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 9 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 173 (accept_3_2 1 9 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 9 173))))))))) (allB_succ 8 173 (allA_succ_of_accept 7 8 173 (accept_3_2 7 8 173 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 8 173 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 8 173
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 8 173
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 8 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 8 173 (accept_3_2 4 8 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 8 173
  (Polychromatic418967fa.accept_6_3_2_5_1_32 3 8 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 8 173 (Polychromatic418967fa.accept_12_2_8_5_1_408 2 8 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 8 173 (accept_3_2 1 8 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 8 173)))))))) (allB_succ 7 173 (allA_of_3_0 7 7 173 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 6 173 (allA_succ_of_accept 5 6 173 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 6 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 6 173 (accept_3_2 4 6 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 6 173 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 6 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 6 173 (Polychromatic418967fa.accept_13_2_6_4_1_1593 2
  6 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 173 (accept_3_2 1 6 173
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 173)))))) (allB_succ 5 173 (allA_succ_of_accept 4 5 173
  (accept_3_2 4 5 173 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 173
  (Polychromatic418967fa.accept_9_3_5_2_1_28 3 5 173 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 5 173 (Polychromatic418967fa.accept_10_2_5_3_1_1408 2 5 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 173 (accept_3_2 1 5 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 5 173))))) (allB_succ 4 173 (allA_of_3_0 4 4 173 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 3 173 (allA_succ_of_accept 2 3 173 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 3 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 173 (accept_3_2 1 3 173 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 3 173))) (allB_succ 2 173 (allA_succ_of_accept 1 2 173 (accept_3_2 1 2 173 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 2 173)) (allB_two
  173)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


