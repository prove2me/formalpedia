-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch190
-- name    : Polychromatic418967fa_Branch190
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:20:38.803821+00:00
-- url     : https://prove2.me/theorems/8faa4b08-5aa3-43f1-a557-fc477b42b74a
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch190_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_190 : allB 190 190 :=
  allB_succ' 2 189 190 (Eq.refl Bool.true) (allA_succ_of_accept 1 189 190 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  189 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 189 190)) (allB_succ' 3 188 190
  (Eq.refl Bool.true) (allA_of_3_1 3 188 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 187 190 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 187 190 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 187 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 187 190 (accept_3_3 2 187 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 187 190 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 187 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 187 190)))) (allB_succ' 5 186 190 (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 186 190 2 2 93 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 186 190 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 186 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 186 190 2 1 93 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 186 190 (Polychromatic418967fa.accept_15_1_6_10_1_23 1 186 190
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186 190))))) (allB_succ' 6 185 190 (Eq.refl
  Bool.true) (allA_of_3_1 6 185 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 184 190 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 184 190 2 3 92 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 184 190 (accept_3_3 5 184 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 184
  190 2 2 92 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  184 190 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 184 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 184 190 2 1 92 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 184 190 (Polychromatic418967fa.accept_12_1_4_10_1_209 1 184 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 184 190))))))) (allB_succ' 8 183 190 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 183 190 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 183 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 183 190 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 183 190
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 183 190 (accept_3_3 5 183 190
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 183 190 (Polychromatic418967fa.accept_9_4_3_1_1_154 4
  183 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 183 190
  (Polychromatic418967fa.accept_21_3_15_1_1_2046 3 183 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 183 190 (accept_3_3 2 183 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  183 190 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 183 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 183 190)))))))) (allB_succ' 9 182 190 (Eq.refl Bool.true) (allA_of_3_1 9 182 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 181 190 (Eq.refl Bool.true) (allA_succ_of_accept 9 181 190
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 181 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 181 190 (accept_3_3 8 181 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  181 190 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 181 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 181 190 (Polychromatic418967fa.accept_15_6_1_10_1_1549 6 181 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 181 190 (accept_3_3 5 181 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 181 190 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 181 190
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 181 190
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 181 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 181 190 (accept_3_3 2 181 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  181 190 (Polychromatic418967fa.accept_13_1_12_8_1_1818 1 181 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 181 190)))))))))) (allB_succ' 11 180 190 (Eq.refl Bool.true) (allA_succ_of_gcd 10 180 190 10 1
  18 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 180 190
  (Polychromatic418967fa.accept_13_9_11_8_1_195 9 180 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 180 190 2 4 90 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 180 190 (Polychromatic418967fa.accept_11_7_4_3_1_302 7 180 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 180 190 2 3 90 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 180 190 5 1 36 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 180 190 2 2 90 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 180 190 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 180 190
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 180 190 2 1 90 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 180 190
  (Polychromatic418967fa.accept_13_1_11_8_1_2562 1 180 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 180 190))))))))))) (allB_succ' 12 179 190 (Eq.refl Bool.true) (allA_of_3_1 12 179 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 13 178 190 (Eq.refl Bool.true) (allA_succ_of_gcd 12 178 190 2 6 89 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 178 190 (accept_3_3 11
  178 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 178 190 2 5 89 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 178 190
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 178 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 178 190 2 4 89 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 178 190 (Polychromatic418967fa.accept_13_7_9_8_1_188 7 178 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 178 190 2 3 89 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 178 190 (accept_3_3 5 178 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 178 190 2 2 89 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 178 190 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 178 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 178 190 2 1 89 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 178 190 (Polychromatic418967fa.accept_11_1_2_3_1_688 1
  178 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 178 190))))))))))))) (allB_succ' 14 177
  190 (Eq.refl Bool.true) (allA_succ_of_accept 13 177 190 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 177 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 177 190
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 177 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 177 190 (accept_3_3 11 177 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 177 190 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 177 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 177 190 (Polychromatic418967fa.accept_15_9_12_10_1_809 9 177 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 177 190 (accept_3_3 8 177 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 177 190 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 177 190
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 177 190
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 177 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 177 190 (accept_3_3 5 177 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  177 190 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 177 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 177 190 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 177 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 177 190 (accept_3_3 2 177 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 190 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 177 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 177 190)))))))))))))) (allB_succ' 15 176 190 (Eq.refl
  Bool.true) (allA_of_3_1 15 176 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 175 190 (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 175 190 5 3 35 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 175 190 (accept_3_3 14 175 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 175 190 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 175 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 175 190 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 175 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 175 190 (accept_3_3 11 175 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 175 190 5 2 35 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 175 190 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 175 190
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 175 190 (accept_3_3 8 175 190
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 175 190 (Polychromatic418967fa.accept_9_7_4_1_1_391 7
  175 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 175 190
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 175 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 175 190 5 1 35 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 175 190 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 175 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 175 190 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 175 190
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 175 190 (accept_3_3 2 175 190
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 175 190 (Polychromatic418967fa.accept_4_1_3_2_1_3 1
  175 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 175 190)))))))))))))))) (allB_succ' 17
  174 190 (Eq.refl Bool.true) (allA_succ_of_gcd 16 174 190 2 8 87 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 174 190 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 174 190
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 174 190 2 7 87 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 174 190
  (Polychromatic418967fa.accept_9_4_3_1_1_154 13 174 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 174 190 2 6 87 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 174 190 (accept_3_3 11 174 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  174 190 2 5 87 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 174 190 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 174 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 174 190 2 4 87 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 174 190 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 174 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 174 190 2 3 87 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 174 190 (accept_3_3 5 174 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 174 190 2 2 87 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 174 190 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 174 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 174 190 2 1 87 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 174 190
  (Polychromatic418967fa.accept_13_1_5_8_1_207 1 174 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 174 190))))))))))))))))) (allB_succ' 18 173 190 (Eq.refl Bool.true) (allA_of_3_1 18 173 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 172 190 (Eq.refl Bool.true) (allA_succ_of_gcd 18 172 190 2 9 86 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 172 190
  (accept_3_3 17 172 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 172 190 2 8 86 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 172 190
  (Polychromatic418967fa.accept_11_4_7_3_1_289 15 172 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 172 190 2 7 86 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 172 190 (Polychromatic418967fa.accept_12_1_4_10_1_209 13 172 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 172 190 2 6 86 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 172 190 (accept_3_3 11 172 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 172 190 2 5 86 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 172 190 (Polychromatic418967fa.accept_13_9_3_8_1_573 9 172 190
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 172 190 2 4 86 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 172 190
  (Polychromatic418967fa.accept_12_7_4_10_1_572 7 172 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 172 190 2 3 86 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 172 190 (accept_3_3 5 172 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 172
  190 2 2 86 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  172 190 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 172 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 172 190 2 1 86 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 172 190 (Polychromatic418967fa.accept_12_1_4_10_1_209 1 172 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 172 190))))))))))))))))))) (allB_succ' 20 171 190 (Eq.refl
  Bool.true) (allA_succ_of_gcd 19 171 190 19 1 9 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 18 171 190 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 171 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 171 190 (accept_3_3 17 171 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 171 190 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 171 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 171 190
  (Polychromatic418967fa.accept_17_15_1_3_1_1488 15 171 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 171 190 (accept_3_3 14 171 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 171 190 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 171 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 171 190 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 171 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 171 190 (accept_3_3 11 171 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 171 190 (Polychromatic418967fa.accept_13_10_2_8_1_2603 10 171 190
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 171 190
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 171 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 171 190 (accept_3_3 8 171 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  171 190 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 171 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 171 190 (Polychromatic418967fa.accept_12_6_3_10_1_224 6 171 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 171 190 (accept_3_3 5 171 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 171 190 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 171 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 171 190
  (Polychromatic418967fa.accept_15_3_6_10_1_1539 3 171 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 171 190 (accept_3_3 2 171 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  171 190 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 171 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 171 190)))))))))))))))))))) (allB_succ' 21 170 190 (Eq.refl Bool.true) (allA_of_3_1 21 170 190
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 169 190 (Eq.refl Bool.true) (allA_succ_of_accept 21 169 190
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 169 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 169 190 (accept_3_3 20 169 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 169 190 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 169 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 169 190 (Polychromatic418967fa.accept_11_7_4_3_1_302 18 169 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 169 190 (accept_3_3 17 169 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 169 190 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 169
  190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 169 190
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 169 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 169 190 (accept_3_3 14 169 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 169 190 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 169 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 169 190 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 169 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 169 190 (accept_3_3 11 169 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 169 190 (Polychromatic418967fa.accept_22_10_15_14_1_11040 10 169 190
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 169 190
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 169 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 169 190 (accept_3_3 8 169 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  169 190 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 169 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 169 190 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 169 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 169 190 (accept_3_3 5 169 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 169 190 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 169 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 169 190
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 169 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 169 190 (accept_3_3 2 169 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  169 190 (Polychromatic418967fa.accept_20_1_9_10_1_6491 1 169 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 169 190)))))))))))))))))))))) (allB_succ' 23 168 190 (Eq.refl Bool.true) (allA_succ_of_gcd 22
  168 190 2 11 84 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 168 190 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 168 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 168 190 2 10 84 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 168 190
  (Polychromatic418967fa.accept_25_19_18_15_1_11029 19 168 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 168 190 2 9 84 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 168 190 (accept_3_3 17 168 190 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 168 190 2 8 84 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 168 190 (Polychromatic418967fa.accept_18_15_6_10_1_5590 15 168 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 168 190 2 7 84 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 168 190
  (Polychromatic418967fa.accept_9_4_6_1_1_393 13 168 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 168 190 2 6 84 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 168 190 (accept_3_3 11 168 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  168 190 2 5 84 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 168 190 (Polychromatic418967fa.accept_13_9_12_8_1_570 9 168 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 168 190 2 4 84 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 168 190 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 168 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 168 190 2 3 84 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 168 190 (accept_3_3 5 168 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 168 190 2 2 84 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 168 190 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 168 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 168 190 2 1 84 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 168 190
  (Polychromatic418967fa.accept_13_1_12_8_1_1818 1 168 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 168 190))))))))))))))))))))))) (allB_succ' 24 167 190 (Eq.refl Bool.true) (allA_of_3_1 24 167 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 166 190 (Eq.refl Bool.true) (allA_succ_of_gcd 24 166 190 2 12 83 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 166 190
  (accept_3_3 23 166 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 166 190 2 11 83 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 166 190
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 166 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 166 190 2 10 83 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 166 190 (Polychromatic418967fa.accept_20_19_6_10_1_3651 19 166 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 166 190 2 9 83 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 166 190 (accept_3_3 17 166 190
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 166 190 2 8 83 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 166 190
  (Polychromatic418967fa.accept_9_6_4_1_1_390 15 166 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 166 190 2 7 83 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 166 190 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 166 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 166 190 2 6 83 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 166 190 (accept_3_3 11 166 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 166 190 2 5 83 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 166 190 (Polychromatic418967fa.accept_15_9_1_10_1_4316 9 166 190
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 166 190 2 4 83 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 166 190
  (Polychromatic418967fa.accept_9_7_4_1_1_391 7 166 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 166 190 2 3 83 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 166 190 (accept_3_3 5 166 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 166
  190 2 2 83 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  166 190 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 166 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 166 190 2 1 83 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 166 190 (Polychromatic418967fa.accept_23_1_5_6_1_11020 1 166 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 166 190))))))))))))))))))))))))) (allB_succ' 26 165 190 (Eq.refl
  Bool.true) (allA_succ_of_gcd 25 165 190 5 5 33 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 24 165 190 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 165 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 165 190 (accept_3_3 23 165 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 165 190 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 165 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 165 190
  (Polychromatic418967fa.accept_20_1_5_10_1_3534 21 165 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 165 190 5 4 33 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 165 190 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 165 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 165 190 (Polychromatic418967fa.accept_12_6_9_10_1_565 18 165
  190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 165 190 (accept_3_3 17 165
  190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 165 190
  (Polychromatic418967fa.accept_9_7_3_1_1_386 16 165 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 165 190 5 3 33 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 165 190 (accept_3_3 14 165 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 165 190 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 165 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 165 190 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 165 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 165 190 (accept_3_3 11 165 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 165 190 5 2 33 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 165 190 (Polychromatic418967fa.accept_16_9_5_14_1_6126 9 165 190
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 165 190 (accept_3_3 8 165 190
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 190 (Polychromatic418967fa.accept_4_3_1_2_1_62 7
  165 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 165 190
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 165 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 165 190 5 1 33 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 165 190 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 165 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 165 190 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 165 190
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 165 190 (accept_3_3 2 165 190
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 190 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  165 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 165 190))))))))))))))))))))))))))
  (allB_succ' 27 164 190 (Eq.refl Bool.true) (allA_of_3_1 27 164 190 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 28 163 190 (Eq.refl Bool.true) (allA_succ_of_accept 27 163 190 (Polychromatic418967fa.accept_6_3_1_4_1_25
  27 163 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 163 190 (accept_3_3 26
  163 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 163 190
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 163 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 163 190 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 163 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 163 190 (accept_3_3 23 163 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 163 190 (Polychromatic418967fa.accept_13_9_7_8_1_1122 22 163 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 163 190
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 163 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 163 190 (accept_3_3 20 163 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 163 190 (Polychromatic418967fa.accept_15_4_13_10_1_1508 19 163 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 163 190 (Polychromatic418967fa.accept_15_3_13_10_1_2332 18 163 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 163 190 (accept_3_3 17 163 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 163 190 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 163
  190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 163 190
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 163 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 163 190 (accept_3_3 14 163 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 163 190 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 163 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 163 190 (Polychromatic418967fa.accept_13_12_7_8_1_1104 12 163 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 163 190 (accept_3_3 11 163 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 163 190 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 163 190
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 163 190
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 163 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 163 190 (accept_3_3 8 163 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  163 190 (Polychromatic418967fa.accept_17_7_10_3_1_1421 7 163 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 163 190 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 163 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 163 190 (accept_3_3 5 163 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 163 190 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 163 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 163 190
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 163 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 163 190 (accept_3_3 2 163 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  163 190 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 163 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 163 190)))))))))))))))))))))))))))) (allB_succ' 29 162 190 (Eq.refl Bool.true) (allA_succ_of_gcd
  28 162 190 2 14 81 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 162 190 (Polychromatic418967fa.accept_11_5_8_3_1_66 27 162 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 162 190 2 13 81 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 162 190 (Polychromatic418967fa.accept_20_5_2_10_1_3576
  25 162 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 162 190 2 12 81 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 162 190
  (accept_3_3 23 162 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 162 190 2 11 81 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 162 190
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 162 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 162 190 2 10 81 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 162 190 (Polychromatic418967fa.accept_21_19_15_1_1_6345 19 162 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 162 190 2 9 81 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 162 190 (accept_3_3 17 162 190
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 162 190 2 8 81 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 162 190
  (Polychromatic418967fa.accept_12_3_6_10_1_576 15 162 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 162 190 2 7 81 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 162 190 (Polychromatic418967fa.accept_15_13_12_10_1_4352 13 162 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 162 190 2 6 81 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 162 190 (accept_3_3 11 162 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 162 190 2 5 81 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 162 190 (Polychromatic418967fa.accept_12_9_6_10_1_1085
  9 162 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 162 190 2 4 81 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 162 190
  (Polychromatic418967fa.accept_15_7_12_10_1_4335 7 162 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 162 190 2 3 81 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 162 190 (accept_3_3 5 162 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 162
  190 2 2 81 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  162 190 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 162 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 162 190 2 1 81 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 162 190 (Polychromatic418967fa.accept_13_1_6_8_1_208 1 162 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162 190))))))))))))))))))))))))))))) (allB_succ' 30 161 190
  (Eq.refl Bool.true) (allA_of_3_1 30 161 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 160 190 (Eq.refl
  Bool.true) (allA_succ_of_gcd 30 160 190 10 3 16 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 160 190 (accept_3_3 29 160 190 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 160 190 2 14 80 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 160 190 (Polychromatic418967fa.accept_17_10_7_3_1_727 27 160 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 160 190 2 13 80 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 160 190 5 5 32 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 160 190 2 12 80 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 160 190 (accept_3_3 23
  160 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 160 190 2 11 80 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 160 190
  (Polychromatic418967fa.accept_9_3_7_1_1_143 21 160 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 160 190 10 2 16 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 160 190 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 160 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 160 190 2 9 80 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 160 190 (accept_3_3 17 160 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 160 190 2 8 80 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 160 190 5 3 32 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 160 190 2 7 80 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 160 190 (Polychromatic418967fa.accept_9_4_7_1_1_379 13
  160 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 160 190 2 6 80 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 160 190 (accept_3_3 11
  160 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 160 190 10 1 16 19 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 160 190
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 160 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 160 190 2 4 80 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 160 190 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 160 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 160 190 2 3 80 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 160 190 5 1 32 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 160 190 2 2 80 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 160 190 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 160 190
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 160 190 2 1 80 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 160 190
  (Polychromatic418967fa.accept_12_1_4_10_1_209 1 160 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 160 190))))))))))))))))))))))))))))))) (allB_succ' 32 159 190 (Eq.refl Bool.true) (allA_succ_of_accept 31
  159 190 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 159 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 159 190 (Polychromatic418967fa.accept_9_3_6_1_1_24 30 159 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 159 190 (accept_3_3 29 159 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 159 190 (Polychromatic418967fa.accept_21_7_12_1_1_952 28 159 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 159 190
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 159 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 159 190 (accept_3_3 26 159 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 159 190 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 159 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 159 190 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 159 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 159 190 (accept_3_3 23 159 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 159 190 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 159 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 159 190
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 159 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 159 190 (accept_3_3 20 159 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 159 190 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 159 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 159 190 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 159 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 159 190 (accept_3_3 17 159 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 159 190 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 159 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 159 190
  (Polychromatic418967fa.accept_20_15_19_10_1_11039 15 159 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 159 190 (accept_3_3 14 159 190 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 159 190 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 159 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 159 190 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 159 190
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 159 190 (accept_3_3 11 159 190
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 159 190 (Polychromatic418967fa.accept_7_3_5_1_1_72 10
  159 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 159 190
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 159 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 159 190 (accept_3_3 8 159 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  159 190 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 159 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 159 190 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 159 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 159 190 (accept_3_3 5 159 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 159 190 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 159 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 159 190
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 159 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 159 190 (accept_3_3 2 159 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  159 190 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 159 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 159 190)))))))))))))))))))))))))))))))) (allB_succ' 33 158 190 (Eq.refl Bool.true) (allA_of_3_1
  33 158 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 157 190 (Eq.refl Bool.true) (allA_succ_of_accept 33
  157 190 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 157 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 157 190 (accept_3_3 32 157 190 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 157 190 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 157 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 157 190 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 157 190
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 157 190 (accept_3_3 29 157 190
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 157 190 (Polychromatic418967fa.accept_12_4_1_10_1_221
  28 157 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 157 190
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 157 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 157 190 (accept_3_3 26 157 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 157 190 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 157 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 157 190 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 157 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 157 190 (accept_3_3 23 157 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 157 190 (Polychromatic418967fa.accept_13_9_1_8_1_1742 22 157 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 157 190
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 157 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 157 190 (accept_3_3 20 157 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 157 190 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 157 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 157 190 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 157 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 157 190 (accept_3_3 17 157 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 157 190 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 157 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 157 190
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 157 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 157 190 (accept_3_3 14 157 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 157 190 (Polychromatic418967fa.accept_17_13_4_3_1_1446 13 157 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 157 190 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 157 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 157 190 (accept_3_3 11 157 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 157 190 (Polychromatic418967fa.accept_16_10_13_14_1_5042 10 157 190
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 157 190
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 157 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 157 190 (accept_3_3 8 157 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  157 190 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 157 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 157 190 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 157 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 157 190 (accept_3_3 5 157 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 157 190 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 157 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 157 190
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 157 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 157 190 (accept_3_3 2 157 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  157 190 (Polychromatic418967fa.accept_15_1_7_10_1_287 1 157 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 157 190)))))))))))))))))))))))))))))))))) (allB_succ' 35 156 190 (Eq.refl Bool.true)
  (allA_succ_of_gcd 34 156 190 2 17 78 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 156 190 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 156 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 156 190 2 16 78 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 156 190
  (Polychromatic418967fa.accept_7_3_2_1_1_225 31 156 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 156 190 2 15 78 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 156 190 (accept_3_3 29 156 190 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 156 190 2 14 78 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 156 190 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 156 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 156 190 2 13 78 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 156 190
  (Polychromatic418967fa.accept_9_7_3_1_1_386 25 156 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 156 190 2 12 78 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 156 190 (accept_3_3 23 156 190 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 156 190 2 11 78 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 156 190 (Polychromatic418967fa.accept_22_21_2_14_1_11038 21 156 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 156 190 2 10 78 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 156 190
  (Polychromatic418967fa.accept_15_4_6_10_1_823 19 156 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 156 190 2 9 78 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 156 190 (accept_3_3 17 156 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  156 190 2 8 78 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 156 190 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 156 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 156 190 2 7 78 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 156 190 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 156 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 156 190 2 6 78 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 156 190 (accept_3_3 11 156 190
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 156 190 2 5 78 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 156 190
  (Polychromatic418967fa.accept_18_9_12_10_1_387 9 156 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 156 190 2 4 78 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 156 190 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 156 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 156 190 2 3 78 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 156 190 (accept_3_3 5 156 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 156 190 2 2 78 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 156 190 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 156 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 156 190 2 1 78 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 156 190 (Polychromatic418967fa.accept_11_1_2_3_1_688 1
  156 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156
  190))))))))))))))))))))))))))))))))))) (allB_succ' 36 155 190 (Eq.refl Bool.true) (allA_of_3_1 36 155 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 154 190 (Eq.refl Bool.true) (allA_succ_of_gcd 36 154 190 2 18 77 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 154 190
  (accept_3_3 35 154 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 154 190 2 17 77 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 154 190
  (Polychromatic418967fa.accept_21_12_7_1_1_9465 33 154 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 154 190 2 16 77 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 154 190 (Polychromatic418967fa.accept_16_15_10_14_1_2872 31 154 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 154 190 2 15 77 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 154 190 (accept_3_3 29 154 190
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 154 190 2 14 77 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 154 190
  (Polychromatic418967fa.accept_13_1_11_8_1_2562 27 154 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 154 190 2 13 77 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 154 190 (Polychromatic418967fa.accept_20_5_14_10_1_1269 25 154 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 154 190 2 12 77 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 154 190 (accept_3_3 23 154 190
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 154 190 2 11 77 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 154 190
  (Polychromatic418967fa.accept_15_6_4_10_1_2319 21 154 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 154 190 2 10 77 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 154 190 (Polychromatic418967fa.accept_13_6_11_8_1_1111 19 154 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 154 190 2 9 77 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 154 190 (accept_3_3 17 154 190
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 154 190 2 8 77 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 154 190
  (Polychromatic418967fa.accept_16_15_10_14_1_2872 15 154 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 154 190 2 7 77 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 154 190 (Polychromatic418967fa.accept_15_13_4_10_1_821 13 154 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 154 190 2 6 77 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 154 190 (accept_3_3 11 154 190
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 154 190 2 5 77 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 154 190
  (Polychromatic418967fa.accept_13_9_11_8_1_195 9 154 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 154 190 2 4 77 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 154 190 (Polychromatic418967fa.accept_15_7_4_10_1_1513 7 154 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 154 190 2 3 77 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 154 190 (accept_3_3 5 154 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 154 190 2 2 77 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 154 190 (Polychromatic418967fa.accept_13_3_11_8_1_1094 3 154 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 154 190 2 1 77 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 154 190 (Polychromatic418967fa.accept_13_1_11_8_1_2562
  1 154 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 154
  190))))))))))))))))))))))))))))))))))))) (allB_succ' 38 153 190 (Eq.refl Bool.true) (allA_succ_of_accept 37 153 190
  (Polychromatic418967fa.accept_6_1_3_4_1_1 37 153 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 153 190 (Polychromatic418967fa.accept_15_6_3_10_1_2341 36 153 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 153 190 (accept_3_3 35 153 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 153 190 (Polychromatic418967fa.accept_25_9_3_15_1_11037 34 153 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 153 190
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 153 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 153 190 (accept_3_3 32 153 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 153 190 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 153 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 153 190 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 153 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 153 190 (accept_3_3 29 153 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 153 190 (Polychromatic418967fa.accept_13_2_10_8_1_1126 28 153 190
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 153 190
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 153 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 153 190 (accept_3_3 26 153 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 153 190 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 153 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 153 190 (Polychromatic418967fa.accept_13_11_10_8_1_1804 24 153 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 153 190 (accept_3_3 23 153 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 153 190 (Polychromatic418967fa.accept_15_7_3_10_1_817 22 153
  190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 153 190
  (Polychromatic418967fa.accept_14_7_13_8_1_2067 21 153 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 153 190 (accept_3_3 20 153 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 153 190 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 153 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 153 190 (Polychromatic418967fa.accept_11_7_10_3_1_633 18 153 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 153 190 (accept_3_3 17 153 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 153 190 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 153 190
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 153 190
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 153 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 153 190 (accept_3_3 14 153 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 153 190 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 153 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 153 190 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 153 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 153 190 (accept_3_3 11 153 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 153 190 (Polychromatic418967fa.accept_22_10_21_14_1_9394 10 153 190
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 153 190
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 153 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 153 190 (accept_3_3 8 153 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  153 190 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 153 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 153 190 (Polychromatic418967fa.accept_12_6_9_10_1_565 6 153 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 153 190 (accept_3_3 5 153 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 190 (Polychromatic418967fa.accept_13_4_10_8_1_1817 4 153 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 153 190
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 153 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 153 190 (accept_3_3 2 153 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  153 190 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 153 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 153 190)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 152 190 (Eq.refl Bool.true)
  (allA_of_3_1 39 152 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 40 151 190 (Eq.refl Bool.true)
  (allA_succ_of_accept 39 151 190 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 151 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 151 190 (accept_3_3 38 151 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 151 190 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 151 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 151 190
  (Polychromatic418967fa.accept_15_6_1_10_1_1549 36 151 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 151 190 (accept_3_3 35 151 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 151 190 (Polychromatic418967fa.accept_20_14_11_10_1_11036 34 151 190 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 151 190 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 151 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 151 190 (accept_3_3 32 151 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 151 190 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 151 190
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 151 190
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 151 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 151 190 (accept_3_3 29 151 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 151 190 (Polychromatic418967fa.accept_11_6_8_3_1_2236 28 151 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 151 190 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 151 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 151 190 (accept_3_3 26 151 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 151 190 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 151 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 151 190
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 151 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 151 190 (accept_3_3 23 151 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 151 190 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 151 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 151 190 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 151 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 151 190 (accept_3_3 20 151 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 151 190 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 151 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 151 190
  (Polychromatic418967fa.accept_14_4_11_8_1_2034 18 151 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 151 190 (accept_3_3 17 151 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 151 190 (Polychromatic418967fa.accept_11_5_8_3_1_66 16 151 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 151 190 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 151 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 151 190 (accept_3_3 14 151 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 151 190 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 151 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 151 190
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 151 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 151 190 (accept_3_3 11 151 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 151 190 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 151 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 151 190 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 151 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 151 190 (accept_3_3 8 151 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 151 190 (Polychromatic418967fa.accept_15_7_1_10_1_305 7 151 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 151 190
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 151 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 151 190 (accept_3_3 5 151 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  151 190 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 151 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 151 190 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 151 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 151 190 (accept_3_3 2 151 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 151 190 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 151 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 151 190))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 41 150 190 (Eq.refl Bool.true) (allA_succ_of_gcd 40 150 190 10 4 15 19 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 150 190
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 150 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 150 190 2 19 75 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 150 190 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 150 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 150 190 2 18 75 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 150 190 5 7 30 38 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 150 190 2 17 75 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 150 190
  (Polychromatic418967fa.accept_7_5_3_1_1_424 33 150 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 150 190 2 16 75 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 150 190 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 150 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 150 190 10 3 15 19 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 150 190 (accept_3_3 29 150 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 150 190 2 14 75 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 150 190 (Polychromatic418967fa.accept_12_3_6_10_1_576
  27 150 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 150 190 2 13 75 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 150 190 5 5 30 38
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 150 190 2 12 75
  95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 150 190
  (accept_3_3 23 150 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 150 190 2 11 75 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 150 190
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 150 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 150 190 10 2 15 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 150 190 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 150 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 150 190 2 9 75 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 150 190 (accept_3_3 17 150 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 150 190 2 8 75 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 150 190 5 3 30 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 150 190 2 7 75 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 150 190 (Polychromatic418967fa.accept_9_4_6_1_1_393 13
  150 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 150 190 2 6 75 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 150 190 (accept_3_3 11
  150 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 150 190 10 1 15 19 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 150 190
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 150 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 150 190 2 4 75 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 150 190 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 150 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 150 190 2 3 75 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 150 190 5 1 30 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 150 190 2 2 75 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 150 190 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 150 190
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 150 190 2 1 75 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 150 190
  (Polychromatic418967fa.accept_13_1_7_8_1_1796 1 150 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 150 190))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 149 190 (Eq.refl Bool.true) (allA_of_3_1 42
  149 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 148 190 (Eq.refl Bool.true) (allA_succ_of_gcd 42 148
  190 2 21 74 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  148 190 (accept_3_3 41 148 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 148 190 2 20 74 95
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 148 190
  (Polychromatic418967fa.accept_9_3_4_1_1_22 39 148 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 148 190 2 19 74 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 148 190 (Polychromatic418967fa.accept_12_1_4_10_1_209 37 148 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 148 190 2 18 74 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 148 190 (accept_3_3 35 148 190
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 148 190 2 17 74 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 148 190
  (Polychromatic418967fa.accept_9_6_4_1_1_390 33 148 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 148 190 2 16 74 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 148 190 (Polychromatic418967fa.accept_12_7_4_10_1_572 31 148 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 148 190 2 15 74 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 148 190 (accept_3_3 29 148 190
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 148 190 2 14 74 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 148 190
  (Polychromatic418967fa.accept_13_1_5_8_1_207 27 148 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 148 190 2 13 74 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 148 190 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 148 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 148 190 2 12 74 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 148 190 (accept_3_3 23 148 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 148 190 2 11 74 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 148 190 (Polychromatic418967fa.accept_9_3_4_1_1_22 21
  148 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 148 190 2 10 74 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 148 190
  (Polychromatic418967fa.accept_11_8_5_3_1_694 19 148 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 148 190 2 9 74 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 148 190 (accept_3_3 17 148 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  148 190 2 8 74 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 148 190 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 148 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 148 190 2 7 74 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 148 190 (Polychromatic418967fa.accept_12_1_4_10_1_209 13 148 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 148 190 2 6 74 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 148 190 (accept_3_3 11 148 190
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 148 190 2 5 74 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 148 190
  (Polychromatic418967fa.accept_16_9_4_14_1_1878 9 148 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 148 190 2 4 74 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 148 190 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 148 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 148 190 2 3 74 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 148 190 (accept_3_3 5 148 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 148 190 2 2 74 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 148 190 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 148 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 148 190 2 1 74 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 148 190 (Polychromatic418967fa.accept_12_1_4_10_1_209 1
  148 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 148
  190))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 147 190 (Eq.refl Bool.true) (allA_succ_of_accept 43 147
  190 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 147 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 147 190 (Polychromatic418967fa.accept_9_6_3_1_1_155 42 147 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 147 190 (accept_3_3 41 147 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 147 190 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 147 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 147 190
  (Polychromatic418967fa.accept_15_9_12_10_1_809 39 147 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 147 190 (accept_3_3 38 147 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 147 190 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 147 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 147 190 (Polychromatic418967fa.accept_13_10_4_8_1_2570 36 147 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 147 190 (accept_3_3 35 147 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 147 190 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 147 190
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 147 190
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 147 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 147 190 (accept_3_3 32 147 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 147 190 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 147 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 147 190 (Polychromatic418967fa.accept_12_6_3_10_1_224 30 147 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 147 190 (accept_3_3 29 147 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 147 190 (Polychromatic418967fa.accept_15_13_12_10_1_4352 28
  147 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 147 190
  (Polychromatic418967fa.accept_14_13_7_8_1_677 27 147 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 147 190 (accept_3_3 26 147 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 147 190 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 147 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 147 190 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 147 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 147 190 (accept_3_3 23 147 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 147 190 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 147 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 147 190
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 147 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 147 190 (accept_3_3 20 147 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 147 190 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 147 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 147 190 (Polychromatic418967fa.accept_11_7_4_3_1_302 18 147 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 147 190 (accept_3_3 17 147 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 147 190 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 147 190
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 147 190
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 147 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 147 190 (accept_3_3 14 147 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 147 190 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 147 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 147 190 (Polychromatic418967fa.accept_13_12_4_8_1_1120 12 147 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 147 190 (accept_3_3 11 147 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 147 190 (Polychromatic418967fa.accept_13_10_4_8_1_2570 10 147
  190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 147 190
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 147 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 147 190 (accept_3_3 8 147 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  147 190 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 147 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 147 190 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 147 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 147 190 (accept_3_3 5 147 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 147 190 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 147 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 147 190
  (Polychromatic418967fa.accept_20_3_7_10_1_11035 3 147 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 147 190 (accept_3_3 2 147 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  147 190 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 147 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 147 190)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 146 190 (Eq.refl Bool.true)
  (allA_of_3_1 45 146 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 46 145 190 (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 145 190 5 9 29 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 145 190 (accept_3_3 44 145 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 145 190 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 145 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 145 190 (Polychromatic418967fa.accept_20_2_5_10_1_3535 42 145 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 145 190 (accept_3_3 41 145 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 145 190 5 8 29 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 145 190 (Polychromatic418967fa.accept_4_3_1_2_1_62 39
  145 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 145 190 (accept_3_3 38
  145 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 145 190
  (Polychromatic418967fa.accept_20_17_5_10_1_3591 37 145 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 145 190 (Polychromatic418967fa.accept_13_10_2_8_1_2603 36 145 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 145 190 5 7 29 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 145 190
  (Polychromatic418967fa.accept_7_6_5_1_1_416 34 145 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 145 190 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 145 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 145 190 (accept_3_3 32 145 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 145 190 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 145 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 145 190 5 6 29 38 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 145 190 (accept_3_3 29 145 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 145 190 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 145
  190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 145 190
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 145 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 145 190 (accept_3_3 26 145 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25
  145 190 5 5 29 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  24 145 190 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 145 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 145 190 (accept_3_3 23 145 190 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 145 190 (Polychromatic418967fa.accept_20_2_5_10_1_3535 22 145 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 145 190 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 145 190
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 145 190 5 4 29 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 145 190
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 145 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 145 190 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 145 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 145 190 (accept_3_3 17 145 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 145 190 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 145 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 145 190 5 3 29 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 145 190 (accept_3_3 14 145 190
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 145 190 (Polychromatic418967fa.accept_7_6_5_1_1_416
  13 145 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 145 190
  (Polychromatic418967fa.accept_11_1_2_3_1_688 12 145 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 145 190 (accept_3_3 11 145 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  145 190 5 2 29 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 145 190 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 145 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 145 190 (accept_3_3 8 145 190 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 145 190 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 145 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 145 190 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 145 190
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 145 190 5 1 29 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 145 190
  (Polychromatic418967fa.accept_7_4_5_1_1_418 4 145 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 145 190 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 145 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 145 190 (accept_3_3 2 145 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 145 190 (Polychromatic418967fa.accept_11_1_2_3_1_688 1 145 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 145 190)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  47 144 190 (Eq.refl Bool.true) (allA_succ_of_gcd 46 144 190 2 23 72 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 144 190 (Polychromatic418967fa.accept_7_3_4_1_1_71 45
  144 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 144 190 2 22 72 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 144 190
  (Polychromatic418967fa.accept_25_18_19_15_1_11034 43 144 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 144 190 2 21 72 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 144 190 (accept_3_3 41 144 190 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 144 190 2 20 72 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 144 190 (Polychromatic418967fa.accept_14_11_4_8_1_664 39 144 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 144 190 2 19 72 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 144 190
  (Polychromatic418967fa.accept_13_11_1_8_1_1776 37 144 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 144 190 2 18 72 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 144 190 (accept_3_3 35 144 190 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 144 190 2 17 72 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 144 190 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 144 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 144 190 2 16 72 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 144 190
  (Polychromatic418967fa.accept_7_3_4_1_1_71 31 144 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 144 190 2 15 72 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 144 190 (accept_3_3 29 144 190 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 144 190 2 14 72 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 144 190 (Polychromatic418967fa.accept_15_12_9_10_1_2326 27 144 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 144 190 2 13 72 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 144 190
  (Polychromatic418967fa.accept_13_12_1_8_1_1779 25 144 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 144 190 2 12 72 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 144 190 (accept_3_3 23 144 190 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 144 190 2 11 72 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 144 190 (Polychromatic418967fa.accept_20_1_4_10_1_3645 21 144 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 144 190 2 10 72 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 144 190
  (Polychromatic418967fa.accept_7_5_4_1_1_412 19 144 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 144 190 2 9 72 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 144 190 (accept_3_3 17 144 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  144 190 2 8 72 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 144 190 (Polychromatic418967fa.accept_20_15_4_10_1_9538 15 144 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 144 190 2 7 72 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 144 190 (Polychromatic418967fa.accept_11_2_1_3_1_683 13 144 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 144 190 2 6 72 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 144 190 (accept_3_3 11 144 190
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 144 190 2 5 72 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 144 190
  (Polychromatic418967fa.accept_13_9_1_8_1_1742 9 144 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 144 190 2 4 72 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 144 190 (Polychromatic418967fa.accept_13_7_1_8_1_1778 7 144 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 144 190 2 3 72 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 144 190 (accept_3_3 5 144 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 144 190 2 2 72 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 144 190 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 144 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 144 190 2 1 72 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 144 190 (Polychromatic418967fa.accept_15_1_9_10_1_2327
  1 144 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144
  190))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 143 190 (Eq.refl Bool.true) (allA_of_3_1 48 143 190
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 142 190 (Eq.refl Bool.true) (allA_succ_of_gcd 48 142 190 2 24
  71 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 142 190
  (accept_3_3 47 142 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 142 190 2 23 71 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 142 190
  (Polychromatic418967fa.accept_7_3_2_1_1_225 45 142 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 142 190 2 22 71 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 142 190 (Polychromatic418967fa.accept_13_4_12_8_1_197 43 142 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 142 190 2 21 71 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 142 190 (accept_3_3 41 142 190
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 142 190 2 20 71 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 142 190
  (Polychromatic418967fa.accept_9_3_7_1_1_143 39 142 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 142 190 2 19 71 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 142 190 (Polychromatic418967fa.accept_18_1_16_10_1_2065 37 142 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 142 190 2 18 71 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 142 190 (accept_3_3 35 142 190
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 142 190 2 17 71 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 142 190
  (Polychromatic418967fa.accept_9_6_7_1_1_145 33 142 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 142 190 2 16 71 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 142 190 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 142 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 142 190 2 15 71 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 142 190 (accept_3_3 29 142 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 142 190 2 14 71 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 142 190 (Polychromatic418967fa.accept_7_6_2_1_1_214 27
  142 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 142 190 2 13 71 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 142 190
  (Polychromatic418967fa.accept_20_5_2_10_1_3576 25 142 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 142 190 2 12 71 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 142 190 (accept_3_3 23 142 190 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 142 190 2 11 71 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 142 190 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 142 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 142 190 2 10 71 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 142 190
  (Polychromatic418967fa.accept_15_4_7_10_1_807 19 142 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 142 190 2 9 71 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 142 190 (accept_3_3 17 142 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  142 190 2 8 71 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 142 190 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 142 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 142 190 2 7 71 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 142 190 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 142 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 142 190 2 6 71 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 142 190 (accept_3_3 11 142 190
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 142 190 2 5 71 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 142 190
  (Polychromatic418967fa.accept_13_9_12_8_1_570 9 142 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 142 190 2 4 71 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 142 190 (Polychromatic418967fa.accept_11_7_10_3_1_633 7 142 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 142 190 2 3 71 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 142 190 (accept_3_3 5 142 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 142 190 2 2 71 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 142 190 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 142 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 142 190 2 1 71 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 142 190 (Polychromatic418967fa.accept_13_1_12_8_1_1818
  1 142 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142
  190))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 141 190 (Eq.refl Bool.true) (allA_succ_of_accept
  49 141 190 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 141 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 141 190 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 141 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 141 190 (accept_3_3 47 141 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 141 190 (Polychromatic418967fa.accept_15_1_6_10_1_23 46 141 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 141 190
  (Polychromatic418967fa.accept_13_6_11_8_1_1111 45 141 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 141 190 (accept_3_3 44 141 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 141 190 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 141 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 141 190 (Polychromatic418967fa.accept_12_6_9_10_1_565 42 141 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 141 190 (accept_3_3 41 141 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 141 190 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 141 190
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 141 190
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 141 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 141 190 (accept_3_3 38 141 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 141 190 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 141 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 141 190 (Polychromatic418967fa.accept_13_10_11_8_1_1770 36 141 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 141 190 (accept_3_3 35 141 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 141 190 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 141 190
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 141 190
  (Polychromatic418967fa.accept_15_3_6_10_1_1539 33 141 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 141 190 (accept_3_3 32 141 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 141 190 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 141 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 141 190 (Polychromatic418967fa.accept_9_3_6_1_1_24 30 141 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 141 190 (accept_3_3 29 141 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 141 190 (Polychromatic418967fa.accept_11_6_9_3_1_1103 28 141 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 141 190
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 141 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 141 190 (accept_3_3 26 141 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 141 190 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 141 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 141 190 (Polychromatic418967fa.accept_18_6_15_10_1_6975 24 141 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 141 190 (accept_3_3 23 141 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 141 190 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 141 190
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 141 190
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 141 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 141 190 (accept_3_3 20 141 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 141 190 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 141 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 141 190 (Polychromatic418967fa.accept_12_6_9_10_1_565 18 141 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 141 190 (accept_3_3 17 141 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 141 190 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 141 190
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 141 190
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 141 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 141 190 (accept_3_3 14 141 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 141 190 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 141 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 141 190 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 141 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 141 190 (accept_3_3 11 141 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 141 190 (Polychromatic418967fa.accept_13_10_11_8_1_1770 10 141 190
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 141 190
  (Polychromatic418967fa.accept_13_9_11_8_1_195 9 141 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 141 190 (accept_3_3 8 141 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  141 190 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 141 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 141 190 (Polychromatic418967fa.accept_11_6_9_3_1_1103 6 141 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 141 190 (accept_3_3 5 141 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 190 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 141 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 141 190
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 141 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 141 190 (accept_3_3 2 141 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  141 190 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 141 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 141 190)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 140 190 (Eq.refl
  Bool.true) (allA_of_3_1 51 140 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 52 139 190 (Eq.refl Bool.true)
  (allA_succ_of_accept 51 139 190 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 139 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 139 190 (accept_3_3 50 139 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 139 190 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 139 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 139 190 (Polychromatic418967fa.accept_9_3_4_1_1_22 48
  139 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 139 190 (accept_3_3 47
  139 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 139 190
  (Polychromatic418967fa.accept_13_7_9_8_1_188 46 139 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 139 190 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 139 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 139 190 (accept_3_3 44 139 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 139 190 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 139 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 139 190 (Polychromatic418967fa.accept_9_6_4_1_1_390
  42 139 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 139 190 (accept_3_3 41
  139 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 139 190
  (Polychromatic418967fa.accept_7_5_6_1_1_407 40 139 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 139 190 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 139 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 139 190 (accept_3_3 38 139 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 139 190 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 139 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 139 190
  (Polychromatic418967fa.accept_15_6_4_10_1_2319 36 139 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 139 190 (accept_3_3 35 139 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 139 190 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 139 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 139 190 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 139 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 139 190 (accept_3_3 32 139 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 139 190 (Polychromatic418967fa.accept_20_11_19_10_1_3568 31 139 190
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 139 190
  (Polychromatic418967fa.accept_7_2_6_1_1_73 30 139 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 139 190 (accept_3_3 29 139 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 139 190 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 139 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 139 190 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 139 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 139 190 (accept_3_3 26 139 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 139 190 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 139 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 139 190
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 139 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 139 190 (accept_3_3 23 139 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 139 190 (Polychromatic418967fa.accept_15_7_4_10_1_1513 22 139 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 139 190 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 139 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 139 190 (accept_3_3 20 139 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 139 190 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 139 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 139 190
  (Polychromatic418967fa.accept_22_18_7_14_1_11033 18 139 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 139 190 (accept_3_3 17 139 190 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 139 190 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 139 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 139 190 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 139 190
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 139 190 (accept_3_3 14 139 190
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 139 190 (Polychromatic418967fa.accept_4_1_3_2_1_3 13
  139 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 139 190
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 139 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 139 190 (accept_3_3 11 139 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 139 190 (Polychromatic418967fa.accept_11_10_7_3_1_3679 10 139 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 139 190 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 139 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 139 190 (accept_3_3 8 139 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 139 190 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 139 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 139 190
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 139 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 139 190 (accept_3_3 5 139 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  139 190 (Polychromatic418967fa.accept_11_4_7_3_1_289 4 139 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 139 190 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 139 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 139 190 (accept_3_3 2 139 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 139 190 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 139 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 139
  190)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 138 190 (Eq.refl Bool.true) (allA_succ_of_gcd
  52 138 190 2 26 69 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 138 190 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 138 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 138 190 2 25 69 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 138 190 (Polychromatic418967fa.accept_9_4_3_1_1_154 49
  138 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 138 190 2 24 69 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 138 190 (accept_3_3 47
  138 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 138 190 2 23 69 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 138 190
  (Polychromatic418967fa.accept_7_3_5_1_1_72 45 138 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 138 190 2 22 69 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 138 190 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 138 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 138 190 2 21 69 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 138 190 (accept_3_3 41 138 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 138 190 2 20 69 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 138 190 (Polychromatic418967fa.accept_7_4_5_1_1_418 39
  138 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 138 190 2 19 69 95 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 138 190
  (Polychromatic418967fa.accept_15_7_3_10_1_817 37 138 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 138 190 2 18 69 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 138 190 (accept_3_3 35 138 190 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 138 190 2 17 69 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 138 190 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 138 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 138 190 2 16 69 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 138 190
  (Polychromatic418967fa.accept_7_3_5_1_1_72 31 138 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 138 190 2 15 69 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 138 190 (accept_3_3 29 138 190 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 138 190 2 14 69 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 138 190 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 138 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 138 190 2 13 69 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 138 190
  (Polychromatic418967fa.accept_7_4_5_1_1_418 25 138 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 138 190 2 12 69 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 138 190 (accept_3_3 23 138 190 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 138 190 2 11 69 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 138 190 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 138 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 138 190 2 10 69 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 138 190
  (Polychromatic418967fa.accept_11_8_6_3_1_661 19 138 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 138 190 2 9 69 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 138 190 (accept_3_3 17 138 190 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  138 190 2 8 69 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 138 190 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 138 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 138 190 2 7 69 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 138 190 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 138 190 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 138 190 2 6 69 95 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 138 190 (accept_3_3 11 138 190
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 138 190 2 5 69 95 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 138 190
  (Polychromatic418967fa.accept_11_9_6_3_1_1668 9 138 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 138 190 2 4 69 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 138 190 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 138 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 138 190 2 3 69 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 138 190 (accept_3_3 5 138 190 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 138 190 2 2 69 95 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 138 190 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 138 190 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 138 190 2 1 69 95 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 138 190 (Polychromatic418967fa.accept_17_1_2_3_1_4668 1
  138 190 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  190)))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_190_segment_000))))))))))))))))))))))))))))))))))))))))))))))))))))


