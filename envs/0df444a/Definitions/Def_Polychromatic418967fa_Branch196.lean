-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch196
-- name    : Polychromatic418967fa_Branch196
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:21:00.360813+00:00
-- url     : https://prove2.me/theorems/b58130ff-6f74-4c77-ac1b-852026ded3f9
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch196_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_196 : allB 196 196 :=
  allB_succ' 2 195 196 (Eq.refl Bool.true) (allA_succ_of_accept 1 195 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  195 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 195 196)) (allB_succ' 3 194 196
  (Eq.refl Bool.true) (allA_of_3_1 3 194 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 193 196 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 193 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 193 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 193 196 (accept_3_3 2 193 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 193 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 193 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 193 196)))) (allB_succ' 5 192 196 (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 192 196 4 1 48 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 192 196 (Polychromatic418967fa.accept_19_3_2_6_1_11398 3 192 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 192 196 2 1 96 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 192 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 192 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 192 196))))) (allB_succ' 6 191 196 (Eq.refl
  Bool.true) (allA_of_3_1 6 191 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 190 196 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 190 196 2 3 95 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 190 196 (accept_3_3 5 190 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 190
  196 2 2 95 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  190 196 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 190 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 190 196 2 1 95 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 190 196 (Polychromatic418967fa.accept_12_1_10_4_1_380 1 190 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 190 196))))))) (allB_succ' 8 189 196 (Eq.refl Bool.true)
  (allA_succ_of_gcd 7 189 196 7 1 27 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 189 196 (Polychromatic418967fa.accept_12_6_9_4_1_96 6 189 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 189 196 (accept_3_3 5 189 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 189 196 (Polychromatic418967fa.accept_11_4_2_9_1_496 4 189 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 189 196 (Polychromatic418967fa.accept_10_3_9_6_1_94 3
  189 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 189 196 (accept_3_3 2 189
  196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 189 196 (Polychromatic418967fa.accept_6_1_3_4_1_1
  1 189 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 189 196)))))))) (allB_succ' 9 188 196
  (Eq.refl Bool.true) (allA_of_3_1 9 188 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 187 196 (Eq.refl
  Bool.true) (allA_succ_of_accept 9 187 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 187 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 187 196 (accept_3_3 8 187 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 187 196 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 187 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 187 196
  (Polychromatic418967fa.accept_13_6_5_1_1_834 6 187 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 187 196 (accept_3_3 5 187 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  187 196 (Polychromatic418967fa.accept_13_4_5_1_1_833 4 187 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 187 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 187 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 187 196 (accept_3_3 2 187 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 187 196 (Polychromatic418967fa.accept_10_1_7_6_1_91 1 187 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 187 196)))))))))) (allB_succ' 11 186 196 (Eq.refl
  Bool.true) (allA_succ_of_gcd 10 186 196 2 5 93 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 186 196 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 186 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 186 196 2 4 93 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 186 196 (Polychromatic418967fa.accept_15_7_6_1_1_1091 7
  186 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 186 196 2 3 93 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 186 196 (accept_3_3 5
  186 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 186 196 2 2 93 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 186 196
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 186 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 186 196 2 1 93 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 186 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 186 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 186 196))))))))))) (allB_succ' 12 185 196 (Eq.refl Bool.true) (allA_of_3_1
  12 185 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 184 196 (Eq.refl Bool.true) (allA_succ_of_gcd 12
  184 196 4 3 46 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  11 184 196 (accept_3_3 11 184 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 184 196 2 5 92 98
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 184 196
  (Polychromatic418967fa.accept_13_9_2_1_1_813 9 184 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 184 196 4 2 46 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 184 196 (Polychromatic418967fa.accept_16_7_8_4_1_689 7 184 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 184 196 2 3 92 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 184 196 (accept_3_3 5 184 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 184 196 4 1 46 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 184 196 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 184 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 184 196 2 1 92 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 184 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 184
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 184 196))))))))))))) (allB_succ' 14 183 196
  (Eq.refl Bool.true) (allA_succ_of_accept 13 183 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 183 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 183 196
  (Polychromatic418967fa.accept_16_12_7_4_1_687 12 183 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 183 196 (accept_3_3 11 183 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 183 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 183 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 183 196 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 183 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 183 196 (accept_3_3 8 183 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 183 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 183 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 183 196
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 183 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 183 196 (accept_3_3 5 183 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  183 196 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 183 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 183 196 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 183 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 183 196 (accept_3_3 2 183 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 183 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 183 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 183 196)))))))))))))) (allB_succ' 15 182 196 (Eq.refl
  Bool.true) (allA_of_3_1 15 182 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 181 196 (Eq.refl Bool.true)
  (allA_succ_of_accept 15 181 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 181 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 181 196 (accept_3_3 14 181 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 181 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 181 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 181 196 (Polychromatic418967fa.accept_9_3_1_7_1_97 12
  181 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 181 196 (accept_3_3 11
  181 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 181 196
  (Polychromatic418967fa.accept_12_10_1_4_1_392 10 181 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 181 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 181 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 181 196 (accept_3_3 8 181 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 181 196 (Polychromatic418967fa.accept_10_7_1_6_1_673 7 181 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 181 196 (Polychromatic418967fa.accept_9_6_1_7_1_577 6
  181 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 181 196 (accept_3_3 5 181
  196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 181 196
  (Polychromatic418967fa.accept_9_4_1_7_1_293 4 181 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 181 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 181 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 181 196 (accept_3_3 2 181 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 181 196 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 181 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 181 196)))))))))))))))) (allB_succ' 17 180 196 (Eq.refl Bool.true)
  (allA_succ_of_gcd 16 180 196 4 4 45 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 180 196 (Polychromatic418967fa.accept_19_15_9_6_1_8667 15 180 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 180 196 2 7 90 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 180 196 (Polychromatic418967fa.accept_11_2_4_9_1_484
  13 180 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 180 196 4 3 45 49
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 180 196
  (accept_3_3 11 180 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 180 196 2 5 90 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 180 196
  (Polychromatic418967fa.accept_13_9_11_1_1_1375 9 180 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 180 196 4 2 45 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 180 196 (Polychromatic418967fa.accept_13_7_11_1_1_2903 7 180 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 180 196 2 3 90 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 180 196 (accept_3_3 5 180 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 180 196 4 1 45 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 180 196 (Polychromatic418967fa.accept_13_3_11_1_1_2122 3 180 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 180 196 2 1 90 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 180 196 (Polychromatic418967fa.accept_17_1_10_9_1_3884
  1 180 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 180 196))))))))))))))))) (allB_succ'
  18 179 196 (Eq.refl Bool.true) (allA_of_3_1 18 179 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 178 196
  (Eq.refl Bool.true) (allA_succ_of_gcd 18 178 196 2 9 89 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 178 196 (accept_3_3 17 178 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 178 196 2 8 89 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 178 196 (Polychromatic418967fa.accept_11_4_2_9_1_496 15 178 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 178 196 2 7 89 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 178 196 (Polychromatic418967fa.accept_10_3_8_6_1_326
  13 178 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 178 196 2 6 89 98
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 178 196
  (accept_3_3 11 178 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 178 196 2 5 89 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 178 196
  (Polychromatic418967fa.accept_21_9_10_7_1_383 9 178 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 178 196 2 4 89 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 178 196 (Polychromatic418967fa.accept_11_7_2_9_1_480 7 178 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 178 196 2 3 89 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 178 196 (accept_3_3 5 178 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 178 196 2 2 89 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 178 196 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 178 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 178 196 2 1 89 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 178 196 (Polychromatic418967fa.accept_12_1_10_4_1_380 1
  178 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 178 196))))))))))))))))))) (allB_succ'
  20 177 196 (Eq.refl Bool.true) (allA_succ_of_accept 19 177 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 177 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 177 196
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 177 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 177 196 (accept_3_3 17 177 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 177 196 (Polychromatic418967fa.accept_21_16_9_7_1_6709 16 177 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 177 196 (Polychromatic418967fa.accept_17_15_7_9_1_1809 15 177 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 177 196 (accept_3_3 14 177 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 177 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 177 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 177 196
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 177 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 177 196 (accept_3_3 11 177 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 177 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 177 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 177 196 (Polychromatic418967fa.accept_13_9_8_1_1_824 9 177 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 177 196 (accept_3_3 8 177 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 177 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 177 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 177 196
  (Polychromatic418967fa.accept_12_6_9_4_1_96 6 177 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 177 196 (accept_3_3 5 177 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  177 196 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 177 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 177 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 177 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 177 196 (accept_3_3 2 177 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 177 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 177 196)))))))))))))))))))) (allB_succ' 21 176 196
  (Eq.refl Bool.true) (allA_of_3_1 21 176 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 175 196 (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 175 196 7 3 25 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 20 175 196 (accept_3_3 20 175 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 175 196 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 175 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 175 196 (Polychromatic418967fa.accept_13_5_6_1_1_822 18 175
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 175 196 (accept_3_3 17 175
  196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 175 196
  (Polychromatic418967fa.accept_13_3_6_1_1_3797 16 175 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 175 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 175 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 175 196 7 2 25 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 175 196
  (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 175 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 175 196 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 175 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 175 196 (accept_3_3 11 175 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 175 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 175 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 175 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 175 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 175 196 (accept_3_3 8 175 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 175
  196 7 1 25 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6
  175 196 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 175 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 175 196 (accept_3_3 5 175 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 175 196 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 175 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 175 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 175 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 175 196 (accept_3_3 2 175 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 175 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 1
  175 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 175 196))))))))))))))))))))))
  (allB_succ' 23 174 196 (Eq.refl Bool.true) (allA_succ_of_gcd 22 174 196 2 11 87 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 174 196
  (Polychromatic418967fa.accept_12_9_6_4_1_402 21 174 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 174 196 2 10 87 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 174 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 174 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 174 196 2 9 87 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 174 196 (accept_3_3 17 174 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 174 196 2 8 87 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 174 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 15
  174 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 174 196 2 7 87 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 174 196
  (Polychromatic418967fa.accept_9_4_3_7_1_296 13 174 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 174 196 2 6 87 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 174 196 (accept_3_3 11 174 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  174 196 2 5 87 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 174 196 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 174 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 174 196 2 4 87 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 174 196 (Polychromatic418967fa.accept_15_7_9_1_1_473 7 174 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 174 196 2 3 87 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 174 196 (accept_3_3 5 174 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 174 196 2 2 87 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 174 196 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 174 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 174 196 2 1 87 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 174 196
  (Polychromatic418967fa.accept_9_1_3_7_1_6 1 174 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 174 196))))))))))))))))))))))) (allB_succ' 24 173 196 (Eq.refl Bool.true) (allA_of_3_1 24 173 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 172 196 (Eq.refl Bool.true) (allA_succ_of_gcd 24 172 196 4 6 43 49
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 172 196
  (accept_3_3 23 172 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 172 196 2 11 86 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 172 196
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 172 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 172 196 4 5 43 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 172 196 (Polychromatic418967fa.accept_13_6_3_1_1_1413 19 172 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 172 196 2 9 86 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 172 196 (accept_3_3 17 172 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 172 196 4 4 43 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 172 196 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 172 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 172 196 2 7 86 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 172 196
  (Polychromatic418967fa.accept_9_4_1_7_1_293 13 172 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 172 196 4 3 43 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 172 196 (accept_3_3 11 172 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  172 196 2 5 86 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 172 196 (Polychromatic418967fa.accept_15_9_7_1_1_1075 9 172 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 172 196 4 2 43 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 172 196 (Polychromatic418967fa.accept_13_7_3_1_1_814 7 172 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 172 196 2 3 86 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 172 196 (accept_3_3 5 172 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 172 196 4 1 43 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 172 196 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 172 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 172 196 2 1 86 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 172 196
  (Polychromatic418967fa.accept_10_1_2_6_1_638 1 172 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 172 196))))))))))))))))))))))))) (allB_succ' 26 171 196 (Eq.refl Bool.true) (allA_succ_of_accept 25 171 196
  (Polychromatic418967fa.accept_6_1_3_4_1_1 25 171 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 171 196 (Polychromatic418967fa.accept_15_9_6_1_1_493 24 171 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 171 196 (accept_3_3 23 171 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 171 196 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 171 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 171 196
  (Polychromatic418967fa.accept_20_1_11_16_1_699 21 171 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 171 196 (accept_3_3 20 171 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 171 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 171 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 171 196 (Polychromatic418967fa.accept_12_6_3_4_1_394 18 171 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 171 196 (accept_3_3 17 171 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 171 196 (Polychromatic418967fa.accept_13_3_2_1_1_2907 16 171
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 171 196
  (Polychromatic418967fa.accept_8_7_3_4_1_404 15 171 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 171 196 (accept_3_3 14 171 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 171 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 171 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 171 196 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 171 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 171 196 (accept_3_3 11 171 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 171 196 (Polychromatic418967fa.accept_15_10_6_1_1_3707 10 171
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 171 196
  (Polychromatic418967fa.accept_13_9_2_1_1_813 9 171 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 171 196 (accept_3_3 8 171 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  171 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 171 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 171 196 (Polychromatic418967fa.accept_12_6_3_4_1_394 6 171 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 171 196 (accept_3_3 5 171 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 171 196 (Polychromatic418967fa.accept_21_4_3_7_1_11420 4 171 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 171 196
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 171 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 171 196 (accept_3_3 2 171 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  171 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 171 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 171 196)))))))))))))))))))))))))) (allB_succ' 27 170 196 (Eq.refl Bool.true) (allA_of_3_1 27 170
  196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 169 196 (Eq.refl Bool.true) (allA_succ_of_accept 27 169
  196 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 169 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 169 196 (accept_3_3 26 169 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 169 196 (Polychromatic418967fa.accept_10_5_9_6_1_697 25 169 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 169 196 (Polychromatic418967fa.accept_11_2_4_9_1_484 24 169 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 169 196 (accept_3_3 23 169 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 169 196 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 169
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 169 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 169 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 169 196 (accept_3_3 20 169 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 169 196 (Polychromatic418967fa.accept_18_1_7_16_1_1342 19 169 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 169 196 (Polychromatic418967fa.accept_15_3_4_1_1_1072 18 169 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 169 196 (accept_3_3 17 169 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 169 196 (Polychromatic418967fa.accept_21_16_1_7_1_6725 16 169
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 169 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 169 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 169 196 (accept_3_3 14 169 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 169 196 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 169 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 169 196 (Polychromatic418967fa.accept_15_12_4_1_1_3746 12 169 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 169 196 (accept_3_3 11 169 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 169 196 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 169
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 169 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 169 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 169 196 (accept_3_3 8 169 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  169 196 (Polychromatic418967fa.accept_20_7_9_16_1_11410 7 169 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 169 196 (Polychromatic418967fa.accept_17_6_16_9_1_5129 6 169 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 169 196 (accept_3_3 5 169 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 169 196 (Polychromatic418967fa.accept_18_4_7_16_1_2307 4 169
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 169 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 169 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 169 196 (accept_3_3 2 169 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  169 196 (Polychromatic418967fa.accept_18_1_7_16_1_1342 1 169 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 169 196)))))))))))))))))))))))))))) (allB_succ' 29 168 196 (Eq.refl Bool.true) (allA_succ_of_gcd
  28 168 196 28 1 6 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 168 196 (Polychromatic418967fa.accept_16_11_8_4_1_2234 27 168 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 168 196 2 13 84 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 168 196 (Polychromatic418967fa.accept_16_9_8_4_1_1354
  25 168 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 168 196 4 6 42 49
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 168 196
  (accept_3_3 23 168 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 168 196 2 11 84 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 168 196 7 3 24 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 168 196 4 5 42 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 168 196
  (Polychromatic418967fa.accept_9_1_6_7_1_285 19 168 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 168 196 2 9 84 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 168 196 (accept_3_3 17 168 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  168 196 4 4 42 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 168 196 (Polychromatic418967fa.accept_13_2_12_1_1_343 15 168 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 168 196 14 1 12 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 168 196 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 168 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 168 196 4 3 42 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 168 196 (accept_3_3 11 168 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 168 196 2 5 84 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 168 196
  (Polychromatic418967fa.accept_16_9_8_4_1_1354 9 168 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 168 196 4 2 42 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 7 168 196 7 1 24 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 168 196 2 3 84 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 168 196 (accept_3_3 5 168 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 168
  196 4 1 42 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  168 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 168 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 168 196 2 1 84 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 168 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 168 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 168 196))))))))))))))))))))))))))))) (allB_succ' 30 167 196
  (Eq.refl Bool.true) (allA_of_3_1 30 167 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 166 196 (Eq.refl
  Bool.true) (allA_succ_of_gcd 30 166 196 2 15 83 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 166 196 (accept_3_3 29 166 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 166 196 2 14 83 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 166 196 (Polychromatic418967fa.accept_16_11_6_4_1_2228 27 166 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 166 196 2 13 83 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 166 196
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 166 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 166 196 2 12 83 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 166 196 (accept_3_3 23 166 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 166 196 2 11 83 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 166 196 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 166 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 166 196 2 10 83 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 166 196
  (Polychromatic418967fa.accept_9_1_4_7_1_7 19 166 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 166 196 2 9 83 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 166 196 (accept_3_3 17 166 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  166 196 2 8 83 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 166 196 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 166 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 166 196 2 7 83 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 166 196 (Polychromatic418967fa.accept_12_1_10_4_1_380 13 166 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 166 196 2 6 83 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 166 196 (accept_3_3 11 166 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 166 196 2 5 83 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 166 196
  (Polychromatic418967fa.accept_13_9_10_1_1_1389 9 166 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 166 196 2 4 83 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 166 196 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 166 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 166 196 2 3 83 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 166 196 (accept_3_3 5 166 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 166 196 2 2 83 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 166 196 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 166 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 166 196 2 1 83 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 166 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 166
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 166 196)))))))))))))))))))))))))))))))
  (allB_succ' 32 165 196 (Eq.refl Bool.true) (allA_succ_of_accept 31 165 196 (Polychromatic418967fa.accept_6_1_3_4_1_1
  31 165 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 165 196
  (Polychromatic418967fa.accept_12_6_9_4_1_96 30 165 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 165 196 (accept_3_3 29 165 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 165 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 165 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 165 196 (Polychromatic418967fa.accept_19_8_13_6_1_7153 27 165 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 165 196 (accept_3_3 26 165 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 165 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 165 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 165 196
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 165 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 165 196 (accept_3_3 23 165 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 165 196 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 165 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 165 196 (Polychromatic418967fa.accept_10_1_5_6_1_649 21 165 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 165 196 (accept_3_3 20 165 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 165 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 165 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 165 196
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 165 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 165 196 (accept_3_3 17 165 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 165 196 (Polychromatic418967fa.accept_22_16_11_20_1_11399 16 165 196 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 165 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 165 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 165 196 (accept_3_3 14 165 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 165 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 165 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 165 196
  (Polychromatic418967fa.accept_16_12_5_4_1_3275 12 165 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 165 196 (accept_3_3 11 165 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 165 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 165 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 165 196 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 165 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 165 196 (accept_3_3 8 165 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 165 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 165 196
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 165 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 165 196 (accept_3_3 5 165 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  165 196 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 165 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 165 196 (Polychromatic418967fa.accept_22_3_11_20_1_11419 3 165 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 165 196 (accept_3_3 2 165 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 165 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 165 196))))))))))))))))))))))))))))))))
  (allB_succ' 33 164 196 (Eq.refl Bool.true) (allA_of_3_1 33 164 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 34 163 196 (Eq.refl Bool.true) (allA_succ_of_accept 33 163 196 (Polychromatic418967fa.accept_6_3_1_4_1_25
  33 163 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 163 196 (accept_3_3 32
  163 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 163 196
  (Polychromatic418967fa.accept_8_7_3_4_1_404 31 163 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 163 196 (Polychromatic418967fa.accept_9_3_1_7_1_97 30 163 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 163 196 (accept_3_3 29 163 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 163 196 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 163 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 163 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 163 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 163 196 (accept_3_3 26 163 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 163 196 (Polychromatic418967fa.accept_15_10_13_1_1_3698 25 163 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 163 196 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 163 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 163 196 (accept_3_3 23 163 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 163 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 163 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 163 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 163 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 163 196 (accept_3_3 20 163 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 163 196 (Polychromatic418967fa.accept_10_9_3_6_1_686 19 163 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 163 196 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 163 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 163 196 (accept_3_3 17 163 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 163 196 (Polychromatic418967fa.accept_13_3_7_1_1_334 16 163
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 163 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 163 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 163 196 (accept_3_3 14 163 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 163 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 163 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 163 196 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 163 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 163 196 (accept_3_3 11 163 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 163 196 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 163 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 163 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 163 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 163 196 (accept_3_3 8 163 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  163 196 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 163 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 163 196 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 163 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 163 196 (accept_3_3 5 163 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 163 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 163 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 163 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 163 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 163 196 (accept_3_3 2 163 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  163 196 (Polychromatic418967fa.accept_16_1_3_4_1_665 1 163 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 163 196)))))))))))))))))))))))))))))))))) (allB_succ' 35 162 196 (Eq.refl Bool.true)
  (allA_succ_of_gcd 34 162 196 2 17 81 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 162 196 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 162 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 162 196 2 16 81 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 162 196
  (Polychromatic418967fa.accept_10_1_2_6_1_638 31 162 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 162 196 2 15 81 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 162 196 (accept_3_3 29 162 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 162 196 2 14 81 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 162 196 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 162 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 162 196 2 13 81 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 162 196
  (Polychromatic418967fa.accept_22_3_8_20_1_11418 25 162 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 162 196 2 12 81 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 162 196 (accept_3_3 23 162 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 162 196 2 11 81 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 162 196 (Polychromatic418967fa.accept_10_1_2_6_1_638 21 162 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 162 196 2 10 81 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 162 196
  (Polychromatic418967fa.accept_15_4_12_1_1_1081 19 162 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 162 196 2 9 81 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 162 196 (accept_3_3 17 162 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  162 196 2 8 81 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 162 196 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 162 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 162 196 2 7 81 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 162 196 (Polychromatic418967fa.accept_15_13_12_1_1_1841 13 162 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 162 196 2 6 81 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 162 196 (accept_3_3 11
  162 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 162 196 2 5 81 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 162 196
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 162 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 162 196 2 4 81 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 162 196 (Polychromatic418967fa.accept_13_7_6_1_1_368 7 162 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 162 196 2 3 81 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 162 196 (accept_3_3 5 162 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 162 196 2 2 81 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 162 196 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 162 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 162 196 2 1 81 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 162 196 (Polychromatic418967fa.accept_10_1_2_6_1_638 1
  162 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162
  196))))))))))))))))))))))))))))))))))) (allB_succ' 36 161 196 (Eq.refl Bool.true) (allA_of_3_1 36 161 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 160 196 (Eq.refl Bool.true) (allA_succ_of_gcd 36 160 196 4 9 40 49
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 160 196
  (accept_3_3 35 160 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 160 196 2 17 80 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 160 196
  (Polychromatic418967fa.accept_19_14_8_6_1_981 33 160 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 160 196 4 8 40 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 160 196 (Polychromatic418967fa.accept_13_5_4_1_1_364 31 160 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 160 196 2 15 80 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 160 196 (accept_3_3 29 160 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 160 196 4 7 40 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 160 196 (Polychromatic418967fa.accept_21_6_13_7_1_8394 27 160
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 160 196 2 13 80 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 160 196
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 25 160 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 160 196 4 6 40 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 160 196 (accept_3_3 23 160 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  160 196 2 11 80 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 160 196 (Polychromatic418967fa.accept_15_6_10_1_1_3675 21 160 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 160 196 4 5 40 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 160 196 (Polychromatic418967fa.accept_17_2_7_9_1_2796
  19 160 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 160 196 2 9 80 98
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 160 196
  (accept_3_3 17 160 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 160 196 4 4 40 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 160 196
  (Polychromatic418967fa.accept_17_15_7_9_1_1809 15 160 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 160 196 2 7 80 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 160 196 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 160 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 160 196 4 3 40 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 160 196 (accept_3_3 11 160 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 160 196 2 5 80 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 160 196 (Polychromatic418967fa.accept_15_9_10_1_1_1062
  9 160 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 160 196 4 2 40 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 160 196
  (Polychromatic418967fa.accept_15_7_10_1_1_1836 7 160 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 160 196 2 3 80 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 160 196 (accept_3_3 5 160 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 160
  196 4 1 40 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  160 196 (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 160 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 160 196 2 1 80 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 160 196 (Polychromatic418967fa.accept_26_1_4_14_1_11417 1 160 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 160 196))))))))))))))))))))))))))))))))))))) (allB_succ'
  38 159 196 (Eq.refl Bool.true) (allA_succ_of_accept 37 159 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 159 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 159 196
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 36 159 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 159 196 (accept_3_3 35 159 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 159 196 (Polychromatic418967fa.accept_29_5_14_22_1_11416 34 159 196 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 159 196 (Polychromatic418967fa.accept_10_3_9_6_1_94 33 159 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 159 196 (accept_3_3 32 159 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 159 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 159 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 159 196
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 159 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 159 196 (accept_3_3 29 159 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 159 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 159 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 159 196 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 159 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 159 196 (accept_3_3 26 159 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 159 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 159 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 159 196
  (Polychromatic418967fa.accept_13_11_3_1_1_1397 24 159 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 159 196 (accept_3_3 23 159 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 159 196 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 159 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 159 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 159 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 159 196 (accept_3_3 20 159 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 159 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 159 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 159 196
  (Polychromatic418967fa.accept_11_7_5_9_1_884 18 159 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 159 196 (accept_3_3 17 159 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 159 196 (Polychromatic418967fa.accept_17_16_6_9_1_7769 16 159 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 159 196 (Polychromatic418967fa.accept_10_5_9_6_1_697 15 159 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 159 196 (accept_3_3 14 159 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 159 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 159 196
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 159 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 159 196 (accept_3_3 11 159 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 159 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 159 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 159 196 (Polychromatic418967fa.accept_18_9_15_16_1_8759 9 159 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 159 196 (accept_3_3 8 159 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 159 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 159 196
  (Polychromatic418967fa.accept_12_6_3_4_1_394 6 159 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 159 196 (accept_3_3 5 159 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  159 196 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 159 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 159 196 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 159 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 159 196 (accept_3_3 2 159 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 159 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 159 196))))))))))))))))))))))))))))))))))))))
  (allB_succ' 39 158 196 (Eq.refl Bool.true) (allA_of_3_1 39 158 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 40 157 196 (Eq.refl Bool.true) (allA_succ_of_accept 39 157 196 (Polychromatic418967fa.accept_6_3_1_4_1_25
  39 157 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 157 196 (accept_3_3 38
  157 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 157 196
  (Polychromatic418967fa.accept_9_1_4_7_1_7 37 157 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 157 196 (Polychromatic418967fa.accept_15_6_7_1_1_93 36 157 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 157 196 (accept_3_3 35 157 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 157 196 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 157 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 157 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 157 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 157 196 (accept_3_3 32 157 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 157 196 (Polychromatic418967fa.accept_10_1_7_6_1_91 31 157 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 157 196 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 157 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 157 196 (accept_3_3 29 157 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 157 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 157 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 157 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 157 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 157 196 (accept_3_3 26 157 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 157 196 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 157 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 157 196 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 157 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 157 196 (accept_3_3 23 157 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 157 196 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 157 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 157 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 157 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 157 196 (accept_3_3 20 157 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 157 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 157 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 157 196 (Polychromatic418967fa.accept_19_18_5_6_1_2004 18 157 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 157 196 (accept_3_3 17 157 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 157 196 (Polychromatic418967fa.accept_21_16_10_7_1_3782 16 157
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 157 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 157 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 157 196 (accept_3_3 14 157 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 157 196 (Polychromatic418967fa.accept_10_3_7_6_1_659 13 157 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 157 196 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 157 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 157 196 (accept_3_3 11 157 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 157 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 157 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 157 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 157 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 157 196 (accept_3_3 8 157 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  157 196 (Polychromatic418967fa.accept_16_7_13_4_1_1348 7 157 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 157 196 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 157 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 157 196 (accept_3_3 5 157 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 157 196 (Polychromatic418967fa.accept_19_4_5_6_1_11402 4 157 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 157 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 157 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 157 196 (accept_3_3 2 157 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  157 196 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 157 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 157 196)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 156 196 (Eq.refl Bool.true)
  (allA_succ_of_gcd 40 156 196 4 10 39 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 156 196 (Polychromatic418967fa.accept_15_9_6_1_1_493 39 156 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 156 196 2 19 78 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 156 196
  (Polychromatic418967fa.accept_9_1_3_7_1_6 37 156 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 156 196 4 9 39 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 156 196 (accept_3_3 35 156 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  156 196 2 17 78 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 156 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 156 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 156 196 4 8 39 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 156 196 (Polychromatic418967fa.accept_9_4_3_7_1_296 31
  156 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 156 196 2 15 78 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 156 196 (accept_3_3 29
  156 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 156 196 4 7 39 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 156 196
  (Polychromatic418967fa.accept_16_11_12_4_1_3195 27 156 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 156 196 2 13 78 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 156 196 (Polychromatic418967fa.accept_15_10_6_1_1_3707 25 156 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 156 196 4 6 39 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 156 196 (accept_3_3 23 156 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 156 196 2 11 78 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 156 196
  (Polychromatic418967fa.accept_16_5_12_4_1_4325 21 156 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 156 196 4 5 39 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 156 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 156 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 156 196 2 9 78 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 156 196 (accept_3_3 17 156 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 156 196 4 4 39 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 156 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 156 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 156 196 2 7 78 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 156 196
  (Polychromatic418967fa.accept_9_4_3_7_1_296 13 156 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 156 196 4 3 39 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 156 196 (accept_3_3 11 156 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  156 196 2 5 78 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 156 196 (Polychromatic418967fa.accept_15_9_6_1_1_493 9 156 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 156 196 4 2 39 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 156 196 (Polychromatic418967fa.accept_11_7_2_9_1_480 7 156 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 156 196 2 3 78 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 156 196 (accept_3_3 5 156 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 156 196 4 1 39 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 156 196 (Polychromatic418967fa.accept_15_3_6_1_1_1834 3 156 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 156 196 2 1 78 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 156 196
  (Polychromatic418967fa.accept_9_1_3_7_1_6 1 156 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 156 196))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 155 196 (Eq.refl Bool.true) (allA_of_3_1 42
  155 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 154 196 (Eq.refl Bool.true) (allA_succ_of_gcd 42 154
  196 14 3 11 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  154 196 (accept_3_3 41 154 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 154 196 2 20 77 98
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 154 196
  (Polychromatic418967fa.accept_9_3_1_7_1_97 39 154 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 154 196 2 19 77 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 154 196 (Polychromatic418967fa.accept_12_1_10_4_1_380 37 154 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 154 196 2 18 77 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 154 196 7 5 22 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 154 196 2 17 77 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 154 196
  (Polychromatic418967fa.accept_9_6_1_7_1_577 33 154 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 154 196 2 16 77 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 154 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 154 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 154 196 2 15 77 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 154 196 (accept_3_3 29 154 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 154 196 14 2 11 14 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 154 196 (Polychromatic418967fa.accept_15_12_4_1_1_3746
  27 154 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 154 196 2 13 77 98
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 154 196
  (Polychromatic418967fa.accept_10_5_4_6_1_319 25 154 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 154 196 2 12 77 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 154 196 (accept_3_3 23 154 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 154 196 2 11 77 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 154 196 7 3 22 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 154 196 2 10 77 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 154 196 (Polychromatic418967fa.accept_12_7_10_4_1_382 19 154 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 154 196 2 9 77 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 154 196 (accept_3_3 17 154 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 154 196 2 8 77 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 154 196
  (Polychromatic418967fa.accept_9_6_1_7_1_577 15 154 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 154 196 14 1 11 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 154 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 154 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 154 196 2 6 77 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 154 196 (accept_3_3 11 154 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 154 196 2 5 77 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 154 196 (Polychromatic418967fa.accept_13_9_11_1_1_1375
  9 154 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 154 196 2 4 77 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 154 196 7 1 22 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 154 196 2 3 77 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 154 196 (accept_3_3 5
  154 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 154 196 2 2 77 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 154 196
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 154 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 154 196 2 1 77 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 154 196 (Polychromatic418967fa.accept_12_1_10_4_1_380 1 154 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 154 196))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 153 196
  (Eq.refl Bool.true) (allA_succ_of_accept 43 153 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 153 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 153 196
  (Polychromatic418967fa.accept_12_6_9_4_1_96 42 153 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 153 196 (accept_3_3 41 153 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 153 196 (Polychromatic418967fa.accept_16_8_9_4_1_630 40 153 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 153 196 (Polychromatic418967fa.accept_10_9_3_6_1_686 39 153 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 153 196 (accept_3_3 38 153 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 153 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 153 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 153 196
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 36 153 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 153 196 (accept_3_3 35 153 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 153 196 (Polychromatic418967fa.accept_11_1_10_9_1_871 34 153 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 153 196 (Polychromatic418967fa.accept_18_15_9_16_1_6029 33 153 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 153 196 (accept_3_3 32 153 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 153 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 153 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 153 196
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 30 153 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 153 196 (accept_3_3 29 153 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 153 196 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 153 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 153 196 (Polychromatic418967fa.accept_10_7_3_6_1_644 27 153 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 153 196 (accept_3_3 26 153 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 153 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 153 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 153 196
  (Polychromatic418967fa.accept_13_11_10_1_1_1409 24 153 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 153 196 (accept_3_3 23 153 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 153 196 (Polychromatic418967fa.accept_13_9_10_1_1_1389 22 153 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 153 196 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 153 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 153 196 (accept_3_3 20 153 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 19
  153 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 153 196
  (Polychromatic418967fa.accept_10_8_3_6_1_685 18 153 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 153 196 (accept_3_3 17 153 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 153 196 (Polychromatic418967fa.accept_21_16_6_7_1_6764 16 153 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 153 196 (Polychromatic418967fa.accept_18_15_9_16_1_6029 15 153 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 153 196 (accept_3_3 14 153 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 153 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 153 196
  (Polychromatic418967fa.accept_11_1_10_9_1_871 12 153 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 153 196 (accept_3_3 11 153 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 153 196 (Polychromatic418967fa.accept_19_10_1_6_1_5755 10 153 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 153 196 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 153 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 153 196 (accept_3_3 8 153 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 153 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 153 196
  (Polychromatic418967fa.accept_12_6_9_4_1_96 6 153 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 153 196 (accept_3_3 5 153 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  153 196 (Polychromatic418967fa.accept_13_4_10_1_1_1390 4 153 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 153 196 (Polychromatic418967fa.accept_19_3_1_6_1_3114 3 153 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 153 196 (accept_3_3 2 153 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 153 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 153 196))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 45 152 196 (Eq.refl Bool.true) (allA_of_3_1 45 152 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 46 151 196 (Eq.refl Bool.true) (allA_succ_of_accept 45 151 196 (Polychromatic418967fa.accept_6_3_1_4_1_25
  45 151 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 151 196 (accept_3_3 44
  151 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 151 196
  (Polychromatic418967fa.accept_8_3_7_4_1_42 43 151 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 151 196 (Polychromatic418967fa.accept_10_2_1_6_1_634 42 151 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 151 196 (accept_3_3 41 151 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 151 196 (Polychromatic418967fa.accept_16_8_7_4_1_2217 40 151 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 151 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 151 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 151 196 (accept_3_3 38 151 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 151 196 (Polychromatic418967fa.accept_10_7_1_6_1_673 37 151 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 151 196 (Polychromatic418967fa.accept_19_17_18_6_1_7192 36 151 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 151 196 (accept_3_3 35 151 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 151 196 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 151
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 151 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 151 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 151 196 (accept_3_3 32 151 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 151 196 (Polychromatic418967fa.accept_13_5_8_1_1_2161 31 151 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 151 196 (Polychromatic418967fa.accept_16_14_7_4_1_3243 30 151 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 151 196 (accept_3_3 29 151 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 151 196 (Polychromatic418967fa.accept_16_12_7_4_1_687 28 151
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 151 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 151 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 151 196 (accept_3_3 26 151 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 151 196 (Polychromatic418967fa.accept_10_5_1_6_1_672 25 151 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 151 196 (Polychromatic418967fa.accept_13_11_8_1_1_3815 24 151 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 151 196 (accept_3_3 23 151 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 151 196 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 151
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 151 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 151 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 151 196 (accept_3_3 20 151 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 151 196 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 151 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 151 196 (Polychromatic418967fa.accept_13_5_8_1_1_2161 18 151 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 151 196 (accept_3_3 17 151 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 151 196 (Polychromatic418967fa.accept_21_16_4_7_1_5191 16 151
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 151 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 151 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 151 196 (accept_3_3 14 151 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 151 196 (Polychromatic418967fa.accept_16_13_7_4_1_3248 13 151 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 151 196 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 151 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 151 196 (accept_3_3 11 151 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 151 196 (Polychromatic418967fa.accept_11_10_8_9_1_492 10 151
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 151 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 151 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 151 196 (accept_3_3 8 151 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  151 196 (Polychromatic418967fa.accept_10_7_1_6_1_673 7 151 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 151 196 (Polychromatic418967fa.accept_13_6_8_1_1_2913 6 151 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 151 196 (accept_3_3 5 151 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 151 196 (Polychromatic418967fa.accept_18_4_7_16_1_2307 4 151 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 151 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 151 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 151 196 (accept_3_3 2 151 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  151 196 (Polychromatic418967fa.accept_17_1_15_9_1_1743 1 151 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 151 196)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 150 196 (Eq.refl Bool.true)
  (allA_succ_of_gcd 46 150 196 2 23 75 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 150 196 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 150 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 150 196 2 22 75 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 150 196
  (Polychromatic418967fa.accept_16_11_6_4_1_2228 43 150 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 150 196 2 21 75 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 150 196 (accept_3_3 41 150 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 150 196 2 20 75 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 150 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 150 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 150 196 2 19 75 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 150 196
  (Polychromatic418967fa.accept_9_1_6_7_1_285 37 150 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 150 196 2 18 75 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 150 196 (accept_3_3 35 150 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 150 196 2 17 75 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 150 196 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 150 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 150 196 2 16 75 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 150 196
  (Polychromatic418967fa.accept_9_4_6_7_1_286 31 150 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 150 196 2 15 75 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 150 196 (accept_3_3 29 150 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 150 196 2 14 75 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 150 196 (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 150 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 150 196 2 13 75 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 150 196
  (Polychromatic418967fa.accept_20_5_10_16_1_9890 25 150 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 150 196 2 12 75 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 150 196 (accept_3_3 23 150 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 150 196 2 11 75 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 150 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 150 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 150 196 2 10 75 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 150 196
  (Polychromatic418967fa.accept_9_1_6_7_1_285 19 150 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 150 196 2 9 75 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 150 196 (accept_3_3 17 150 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  150 196 2 8 75 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 150 196 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 150 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 150 196 2 7 75 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 150 196 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 150 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 150 196 2 6 75 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 150 196 (accept_3_3 11 150 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 150 196 2 5 75 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 150 196
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 150 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 150 196 2 4 75 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 150 196 (Polychromatic418967fa.accept_26_7_20_14_1_11415 7 150 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 150 196 2 3 75 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 150 196 (accept_3_3 5 150 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 150 196 2 2 75 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 150 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 150 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 150 196 2 1 75 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 150 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 1
  150 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  196))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 149 196 (Eq.refl Bool.true) (allA_of_3_1 48 149 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 148 196 (Eq.refl Bool.true) (allA_succ_of_gcd 48 148 196 4 12
  37 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 148 196
  (accept_3_3 47 148 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 148 196 2 23 74 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 148 196
  (Polychromatic418967fa.accept_13_6_5_1_1_834 45 148 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 148 196 4 11 37 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 148 196 (Polychromatic418967fa.accept_10_3_8_6_1_326 43 148 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 148 196 2 21 74 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 148 196 (accept_3_3 41 148 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 148 196 4 10 37 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 148 196 (Polychromatic418967fa.accept_9_3_4_7_1_89 39
  148 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 148 196 2 19 74 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 148 196
  (Polychromatic418967fa.accept_9_1_4_7_1_7 37 148 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 148 196 4 9 37 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 148 196 (accept_3_3 35 148 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  148 196 2 17 74 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 148 196 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 148 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 148 196 4 8 37 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 148 196
  (Polychromatic418967fa.accept_17_14_12_9_1_2774 31 148 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 148 196 2 15 74 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 148 196 (accept_3_3 29 148 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 148 196 4 7 37 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 148 196 (Polychromatic418967fa.accept_15_12_13_1_1_3695 27 148 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 148 196 2 13 74 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 148 196
  (Polychromatic418967fa.accept_13_12_5_1_1_1383 25 148 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 148 196 4 6 37 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 148 196 (accept_3_3 23 148 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  148 196 2 11 74 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 148 196 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 148 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 148 196 4 5 37 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 148 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 19
  148 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 148 196 2 9 74 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 148 196 (accept_3_3 17
  148 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 148 196 4 4 37 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 148 196
  (Polychromatic418967fa.accept_9_6_4_7_1_300 15 148 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 148 196 2 7 74 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 148 196 (Polychromatic418967fa.accept_10_3_8_6_1_326 13 148 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 148 196 4 3 37 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 148 196 (accept_3_3 11 148 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 148 196 2 5 74 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 148 196 (Polychromatic418967fa.accept_13_9_5_1_1_1382 9 148 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 148 196 4 2 37 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 148 196
  (Polychromatic418967fa.accept_11_7_5_9_1_884 7 148 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 148 196 2 3 74 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 148 196 (accept_3_3 5 148 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 148
  196 4 1 37 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  148 196 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 148 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 148 196 2 1 74 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 148 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 148 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 148 196)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 50 147 196 (Eq.refl Bool.true) (allA_succ_of_gcd 49 147 196 49 1 3 4 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 147 196
  (Polychromatic418967fa.accept_19_10_14_6_1_5819 48 147 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 147 196 (accept_3_3 47 147 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 147 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 147 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 147 196 (Polychromatic418967fa.accept_19_7_14_6_1_9987 45 147
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 147 196 (accept_3_3 44 147
  196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 147 196 (Polychromatic418967fa.accept_6_1_3_4_1_1
  43 147 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 147 196 7 6 21 28
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 147 196
  (accept_3_3 41 147 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 147 196
  (Polychromatic418967fa.accept_9_4_3_7_1_296 40 147 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 147 196 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 147 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 147 196 (accept_3_3 38 147 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 147 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 147 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 147 196
  (Polychromatic418967fa.accept_13_10_4_1_1_2142 36 147 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 147 196 7 5 21 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 147 196 (Polychromatic418967fa.accept_15_4_12_1_1_1081 34 147 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 147 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 147 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 147 196 (accept_3_3 32 147 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 147 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 31
  147 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 147 196
  (Polychromatic418967fa.accept_12_6_3_4_1_394 30 147 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 147 196 (accept_3_3 29 147 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28
  147 196 7 4 21 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  27 147 196 (Polychromatic418967fa.accept_19_8_14_6_1_5802 27 147 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 147 196 (accept_3_3 26 147 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 147 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 147 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 147 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 147 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 147 196 (accept_3_3 23 147 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 147 196 (Polychromatic418967fa.accept_9_4_3_7_1_296
  22 147 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 147 196 7 3 21 28
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 147 196
  (accept_3_3 20 147 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 196
  (Polychromatic418967fa.accept_6_1_3_4_1_1 19 147 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 147 196 (Polychromatic418967fa.accept_12_6_3_4_1_394 18 147 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 147 196 (accept_3_3 17 147 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 147 196 (Polychromatic418967fa.accept_13_3_4_1_1_363 16 147 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 147 196
  (Polychromatic418967fa.accept_8_7_3_4_1_404 15 147 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 147 196 7 2 21 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 147 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 147 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 147 196 (Polychromatic418967fa.accept_16_12_3_4_1_4317 12 147
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 147 196 (accept_3_3 11 147
  196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 147 196 (Polychromatic418967fa.accept_9_1_3_7_1_6
  10 147 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 147 196
  (Polychromatic418967fa.accept_19_9_14_6_1_2014 9 147 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 147 196 (accept_3_3 8 147 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 147
  196 7 1 21 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6
  147 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 147 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 147 196 (accept_3_3 5 147 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 147 196 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 147 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 147 196 (Polychromatic418967fa.accept_10_3_7_6_1_659 3 147 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 147 196 (accept_3_3 2 147 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  147 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 147
  196)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 146 196 (Eq.refl Bool.true) (allA_of_3_1 51 146
  196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 52 145 196 (Eq.refl Bool.true) (allA_succ_of_accept 51 145
  196 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 145 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 145 196 (accept_3_3 50 145 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 145 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 145 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 145 196 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 145 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 145 196 (accept_3_3 47 145 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 145 196 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 145 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 145 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 145 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 145 196 (accept_3_3 44 145 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 145 196 (Polychromatic418967fa.accept_15_13_10_1_1_1862 43 145 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 145 196 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 145 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 145 196 (accept_3_3 41 145 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 145 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 145 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 145 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 145 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 145 196 (accept_3_3 38 145 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 145 196 (Polychromatic418967fa.accept_8_5_1_4_1_628 37 145 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 145 196 (Polychromatic418967fa.accept_15_6_10_1_1_3675 36 145 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 145 196 (accept_3_3 35 145 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 145 196 (Polychromatic418967fa.accept_10_4_5_6_1_651 34 145
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 145 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 145 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 145 196 (accept_3_3 32 145 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 145 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 145 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 145 196 (Polychromatic418967fa.accept_9_3_1_7_1_97 30 145 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 145 196 (accept_3_3 29 145 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 145 196 (Polychromatic418967fa.accept_15_13_10_1_1_1862 28 145 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 145 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 145 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 145 196 (accept_3_3 26 145 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 145 196 (Polychromatic418967fa.accept_13_12_2_1_1_2909 25 145 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 145 196 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 145 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 145 196 (accept_3_3 23 145 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 145 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 145 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 145 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 145 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 145 196 (accept_3_3 20 145 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 145 196 (Polychromatic418967fa.accept_10_9_5_6_1_691 19 145 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 145 196 (Polychromatic418967fa.accept_11_7_2_9_1_480 18 145 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 145 196 (accept_3_3 17 145 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 145 196 (Polychromatic418967fa.accept_13_3_2_1_1_2907 16 145
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 145 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 145 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 145 196 (accept_3_3 14 145 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 145 196 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 145 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 145 196 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 145 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 145 196 (accept_3_3 11 145 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 145 196 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 145 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 145 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 145 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 145 196 (accept_3_3 8 145 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  145 196 (Polychromatic418967fa.accept_11_7_2_9_1_480 7 145 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 145 196 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 145 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 145 196 (accept_3_3 5 145 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 145 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 145 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 145 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 145 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 145 196 (accept_3_3 2 145 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  145 196 (Polychromatic418967fa.accept_10_1_5_6_1_649 1 145 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 145 196)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 144 196 (Eq.refl
  Bool.true) (allA_succ_of_gcd 52 144 196 4 13 36 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 144 196 (Polychromatic418967fa.accept_15_6_9_1_1_1823 51 144 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 144 196 2 25 72 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 144 196
  (Polychromatic418967fa.accept_32_17_16_4_1_11414 49 144 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 144 196 4 12 36 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 144 196 (accept_3_3 47 144 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 144 196 2 23 72 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 144 196 (Polychromatic418967fa.accept_10_5_4_6_1_319 45 144 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 144 196 4 11 36 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 144 196
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 43 144 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 144 196 2 21 72 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 144 196 (accept_3_3 41 144 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 144 196 4 10 36 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 144 196 (Polychromatic418967fa.accept_19_1_11_6_1_7152 39 144 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 144 196 2 19 72 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 144 196
  (Polychromatic418967fa.accept_15_7_9_1_1_473 37 144 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 144 196 4 9 36 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 144 196 (accept_3_3 35 144 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  144 196 2 17 72 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 144 196 (Polychromatic418967fa.accept_17_16_8_9_1_1772 33 144 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 144 196 4 8 36 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 144 196
  (Polychromatic418967fa.accept_21_10_18_7_1_5212 31 144 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 144 196 2 15 72 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 144 196 (accept_3_3 29 144 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 144 196 4 7 36 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 144 196 (Polychromatic418967fa.accept_21_6_18_7_1_3764 27 144 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 144 196 2 13 72 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 144 196 (Polychromatic418967fa.accept_10_5_4_6_1_319
  25 144 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 144 196 4 6 36 49
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 144 196
  (accept_3_3 23 144 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 144 196 2 11 72 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 144 196
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 21 144 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 144 196 4 5 36 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 144 196 (Polychromatic418967fa.accept_21_19_18_7_1_8388 19 144 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 144 196 2 9 72 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 144 196 (accept_3_3 17 144 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 144 196 4 4 36 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 144 196 (Polychromatic418967fa.accept_10_5_4_6_1_319
  15 144 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 144 196 2 7 72 98
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 144 196
  (Polychromatic418967fa.accept_19_13_11_6_1_3128 13 144 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 144 196 4 3 36 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 144 196 (accept_3_3 11 144 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 144 196 2 5 72 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 144 196 (Polychromatic418967fa.accept_21_9_18_7_1_5180 9 144 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 144 196 4 2 36 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 144 196 (Polychromatic418967fa.accept_15_7_9_1_1_473 7 144 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 144 196 2 3 72 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 144 196 (accept_3_3 5 144 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 144 196 4 1 36 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 144 196
  (Polychromatic418967fa.accept_25_3_19_21_1_11413 3 144 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 144 196 2 1 72 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 144 196 (Polychromatic418967fa.accept_17_1_8_9_1_1810 1 144 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144 196)))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 54 143 196 (Eq.refl Bool.true) (allA_of_3_1 54 143 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 55 142 196 (Eq.refl Bool.true) (allA_succ_of_gcd 54 142 196 2 27 71 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 142 196 (accept_3_3 53 142 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 142 196 2 26 71 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 142 196 (Polychromatic418967fa.accept_10_1_2_6_1_638
  51 142 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 142 196 2 25 71 98
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 142 196
  (Polychromatic418967fa.accept_12_1_10_4_1_380 49 142 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 142 196 2 24 71 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 142 196 (accept_3_3 47 142 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 142 196 2 23 71 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 142 196 (Polychromatic418967fa.accept_11_1_10_9_1_871 45 142 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 142 196 2 22 71 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 142 196
  (Polychromatic418967fa.accept_12_7_10_4_1_382 43 142 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 142 196 2 21 71 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 142 196 (accept_3_3 41 142 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 142 196 2 20 71 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 142 196 (Polychromatic418967fa.accept_15_9_7_1_1_1075 39 142 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 142 196 2 19 71 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 142 196
  (Polychromatic418967fa.accept_12_1_10_4_1_380 37 142 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 142 196 2 18 71 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 142 196 (accept_3_3 35 142 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 142 196 2 17 71 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 142 196 (Polychromatic418967fa.accept_16_1_14_4_1_3220 33 142 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 142 196 2 16 71 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 142 196
  (Polychromatic418967fa.accept_10_1_2_6_1_638 31 142 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 142 196 2 15 71 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 142 196 (accept_3_3 29 142 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 142 196 2 14 71 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 142 196 (Polychromatic418967fa.accept_21_6_16_7_1_3714 27 142 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 142 196 2 13 71 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 142 196
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 142 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 142 196 2 12 71 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 142 196 (accept_3_3 23 142 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 142 196 2 11 71 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 142 196 (Polychromatic418967fa.accept_10_1_2_6_1_638 21 142 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 142 196 2 10 71 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 142 196
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 19 142 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 142 196 2 9 71 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 142 196 (accept_3_3 17 142 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  142 196 2 8 71 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 142 196 (Polychromatic418967fa.accept_13_2_12_1_1_343 15 142 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 142 196 2 7 71 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 142 196 (Polychromatic418967fa.accept_12_1_10_4_1_380 13 142 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 142 196 2 6 71 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 142 196 (accept_3_3 11 142 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 142 196 2 5 71 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 142 196
  (Polychromatic418967fa.accept_15_9_7_1_1_1075 9 142 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 142 196 2 4 71 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 142 196 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 142 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 142 196 2 3 71 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 142 196 (accept_3_3 5 142 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 142 196 2 2 71 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 142 196 (Polychromatic418967fa.accept_17_3_6_9_1_2761 3 142 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 142 196 2 1 71 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 142 196 (Polychromatic418967fa.accept_10_1_2_6_1_638 1
  142 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142
  196))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 141 196 (Eq.refl Bool.true)
  (allA_succ_of_accept 55 141 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 141 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 141 196 (Polychromatic418967fa.accept_12_6_9_4_1_96 54 141 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 141 196 (accept_3_3 53 141 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 141 196 (Polychromatic418967fa.accept_10_2_1_6_1_634
  52 141 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 141 196
  (Polychromatic418967fa.accept_13_12_11_1_1_2920 51 141 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 141 196 (accept_3_3 50 141 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 141 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 141 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 141 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 48 141 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 141 196 (accept_3_3 47 141 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 141 196 (Polychromatic418967fa.accept_9_1_6_7_1_285
  46 141 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 141 196
  (Polychromatic418967fa.accept_10_5_1_6_1_672 45 141 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 141 196 (accept_3_3 44 141 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 141 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 141 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 141 196 (Polychromatic418967fa.accept_10_2_1_6_1_634 42 141 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 141 196 (accept_3_3 41 141 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 141 196 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 141 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 141 196
  (Polychromatic418967fa.accept_9_3_6_7_1_562 39 141 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 141 196 (accept_3_3 38 141 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 141 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 141 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 141 196 (Polychromatic418967fa.accept_13_10_11_1_1_2152 36 141 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 141 196 (accept_3_3 35 141 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 141 196 (Polychromatic418967fa.accept_13_8_11_1_1_3789 34 141
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 141 196
  (Polychromatic418967fa.accept_8_1_5_4_1_388 33 141 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 141 196 (accept_3_3 32 141 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 141 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 141 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 141 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 30 141 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 141 196 (accept_3_3 29 141 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 141 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 141 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 141 196
  (Polychromatic418967fa.accept_10_7_1_6_1_673 27 141 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 141 196 (accept_3_3 26 141 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 141 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 141 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 141 196 (Polychromatic418967fa.accept_15_9_6_1_1_493 24 141 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 141 196 (accept_3_3 23 141 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 141 196 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 141 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 141 196
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 141 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 141 196 (accept_3_3 20 141 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 141 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 141 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 141 196 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 141 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 141 196 (accept_3_3 17 141 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 141 196 (Polychromatic418967fa.accept_13_3_11_1_1_2122 16 141 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 141 196
  (Polychromatic418967fa.accept_10_5_1_6_1_672 15 141 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 141 196 (accept_3_3 14 141 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 141 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 141 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 141 196 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 141 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 141 196 (accept_3_3 11 141 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 141 196 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 141 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 141 196
  (Polychromatic418967fa.accept_8_1_5_4_1_388 9 141 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 141 196 (accept_3_3 8 141 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  141 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 141 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 141 196 (Polychromatic418967fa.accept_12_6_9_4_1_96 6 141 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 141 196 (accept_3_3 5 141 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 196 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 141 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 141 196
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 141 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 141 196 (accept_3_3 2 141 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  141 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 141 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 141 196)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 140 196 (Eq.refl
  Bool.true) (allA_of_3_1 57 140 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 58 139 196 (Eq.refl Bool.true)
  (allA_succ_of_accept 57 139 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 139 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 139 196 (accept_3_3 56 139 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 139 196 (Polychromatic418967fa.accept_8_7_3_4_1_404 55 139 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 139 196 (Polychromatic418967fa.accept_13_2_9_1_1_67
  54 139 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 139 196 (accept_3_3 53
  139 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 139 196
  (Polychromatic418967fa.accept_17_1_3_9_1_958 52 139 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 139 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 139 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 139 196 (accept_3_3 50 139 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 139 196 (Polychromatic418967fa.accept_11_5_7_9_1_2696 49 139 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 139 196
  (Polychromatic418967fa.accept_9_3_4_7_1_89 48 139 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 139 196 (accept_3_3 47 139 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 139 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 139 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 139 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 139 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 139 196 (accept_3_3 44 139 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 139 196 (Polychromatic418967fa.accept_10_3_9_6_1_94 43 139 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 139 196
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 139 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 139 196 (accept_3_3 41 139 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 139 196 (Polychromatic418967fa.accept_16_8_11_4_1_3290 40 139 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 139 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 139 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 139 196 (accept_3_3 38 139 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 139 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 139 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 139 196
  (Polychromatic418967fa.accept_13_10_9_1_1_5609 36 139 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 139 196 (accept_3_3 35 139 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 139 196 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 139 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 139 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 139 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 139 196 (accept_3_3 32 139 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 139 196 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 139 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 139 196
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 139 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 139 196 (accept_3_3 29 139 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 139 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 139 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 139 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 139 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 139 196 (accept_3_3 26 139 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 139 196 (Polychromatic418967fa.accept_10_5_9_6_1_697 25 139 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 139 196
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 139 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 139 196 (accept_3_3 23 139 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 139 196 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 139 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 139 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 139 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 139 196 (accept_3_3 20 139 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 139 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 139 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 139 196
  (Polychromatic418967fa.accept_13_5_9_1_1_1405 18 139 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 139 196 (accept_3_3 17 139 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 139 196 (Polychromatic418967fa.accept_11_5_7_9_1_2696 16 139 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 139 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 139 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 139 196 (accept_3_3 14 139 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 139 196 (Polychromatic418967fa.accept_10_3_9_6_1_94 13 139 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 139 196
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 139 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 139 196 (accept_3_3 11 139 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 139 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 139 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 139 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 139 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 139 196 (accept_3_3 8 139 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 139 196 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 139 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 139 196
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 139 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 139 196 (accept_3_3 5 139 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  139 196 (Polychromatic418967fa.accept_21_4_13_7_1_8386 4 139 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 139 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 139 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 139 196 (accept_3_3 2 139 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 139 196 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 139 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 139
  196)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 138 196 (Eq.refl Bool.true)
  (allA_succ_of_gcd 58 138 196 2 29 69 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 138 196 (Polychromatic418967fa.accept_12_9_6_4_1_402 57 138 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 138 196 2 28 69 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 138 196
  (Polychromatic418967fa.accept_9_1_3_7_1_6 55 138 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 138 196 2 27 69 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 138 196 (accept_3_3 53 138 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 138 196 2 26 69 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 138 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 51 138 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 138 196 2 25 69 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 138 196
  (Polychromatic418967fa.accept_9_4_3_7_1_296 49 138 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 138 196 2 24 69 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 138 196 (accept_3_3 47 138 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 138 196 2 23 69 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 138 196 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 138 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 138 196 2 22 69 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 138 196
  (Polychromatic418967fa.accept_10_3_8_6_1_326 43 138 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 138 196 2 21 69 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 138 196 (accept_3_3 41 138 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 138 196 2 20 69 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 138 196 (Polychromatic418967fa.accept_12_3_6_4_1_400 39 138 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 138 196 2 19 69 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 138 196
  (Polychromatic418967fa.accept_9_1_3_7_1_6 37 138 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 138 196 2 18 69 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 138 196 (accept_3_3 35 138 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 138 196 2 17 69 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 138 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 138 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 138 196 2 16 69 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 138 196
  (Polychromatic418967fa.accept_9_4_3_7_1_296 31 138 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 138 196 2 15 69 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 138 196 (accept_3_3 29 138 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 138 196 2 14 69 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 138 196 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 138 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 138 196 2 13 69 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 138 196
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 25 138 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 138 196 2 12 69 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 138 196 (accept_3_3 23 138 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 138 196 2 11 69 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 138 196 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 138 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 138 196 2 10 69 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 138 196
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 138 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 138 196 2 9 69 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 138 196 (accept_3_3 17 138 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  138 196 2 8 69 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 138 196 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 138 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 138 196 2 7 69 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 138 196 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 138 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 138 196 2 6 69 98 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 138 196 (accept_3_3 11 138 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 138 196 2 5 69 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 138 196
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 138 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 138 196 2 4 69 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 138 196 (Polychromatic418967fa.accept_13_7_8_1_1_2145 7 138 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 138 196 2 3 69 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 138 196 (accept_3_3 5 138 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 138 196 2 2 69 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 138 196 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 138 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 138 196 2 1 69 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 138 196 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 138
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  196))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 137 196 (Eq.refl Bool.true) (allA_of_3_1
  60 137 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 61 136 196 (Eq.refl Bool.true) (allA_succ_of_gcd 60
  136 196 4 15 34 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 136 196 (accept_3_3 59 136 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58
  136 196 2 29 68 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 136 196 (Polychromatic418967fa.accept_9_3_1_7_1_97 57 136 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 136 196 4 14 34 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 136 196 (Polychromatic418967fa.accept_13_3_6_1_1_3797
  55 136 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 136 196 2 27 68 98
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 136 196
  (accept_3_3 53 136 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 136 196 4 13 34 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 136 196
  (Polychromatic418967fa.accept_9_6_1_7_1_577 51 136 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 136 196 2 25 68 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 136 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 136 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 136 196 4 12 34 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 136 196 (accept_3_3 47 136 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 136 196 2 23 68 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 136 196 (Polychromatic418967fa.accept_16_13_8_4_1_3250
  45 136 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 136 196 4 11 34 49
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 136 196
  (Polychromatic418967fa.accept_16_11_8_4_1_2234 43 136 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 136 196 2 21 68 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 136 196 (accept_3_3 41 136 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 136 196 4 10 34 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 136 196 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 136 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 136 196 2 19 68 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 136 196
  (Polychromatic418967fa.accept_16_5_8_4_1_5418 37 136 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 136 196 4 9 34 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 136 196 (accept_3_3 35 136 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  136 196 2 17 68 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 136 196 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 136 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 136 196 4 8 34 49 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 136 196 (Polychromatic418967fa.accept_9_4_1_7_1_293 31
  136 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 136 196 2 15 68 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 136 196 (accept_3_3 29
  136 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 136 196 4 7 34 49 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 136 196
  (Polychromatic418967fa.accept_16_11_8_4_1_2234 27 136 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 136 196 2 13 68 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 136 196 (Polychromatic418967fa.accept_16_9_8_4_1_1354 25 136 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 136 196 4 6 34 49 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 136 196 (accept_3_3 23 136 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 136 196 2 11 68 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 136 196
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 136 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 136 196 4 5 34 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 136 196 (Polychromatic418967fa.accept_16_3_8_4_1_3279 19 136 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 136 196 2 9 68 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 136 196 (accept_3_3 17 136 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 136 196 4 4 34 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 136 196 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 136 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 136 196 2 7 68 98 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 136 196
  (Polychromatic418967fa.accept_9_4_1_7_1_293 13 136 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 136 196 4 3 34 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 136 196 (accept_3_3 11 136 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  136 196 2 5 68 98 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 136 196 (Polychromatic418967fa.accept_13_9_6_1_1_2902 9 136 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 136 196 4 2 34 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 136 196 (Polychromatic418967fa.accept_13_7_6_1_1_368 7 136 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 136 196 2 3 68 98 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 136 196 (accept_3_3 5 136 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 136 196 4 1 34 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 136 196 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 136 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 136 196 2 1 68 98 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 136 196
  (Polychromatic418967fa.accept_16_1_8_4_1_4334 1 136 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 136 196))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 135 196 (Eq.refl
  Bool.true) (allA_succ_of_accept 61 135 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 135 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 135 196 (Polychromatic418967fa.accept_13_8_5_1_1_1381
  60 135 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 135 196 (accept_3_3 59
  135 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 135 196
  (Polychromatic418967fa.accept_13_6_5_1_1_834 58 135 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 135 196 (Polychromatic418967fa.accept_17_6_16_9_1_5129 57 135 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 135 196 (accept_3_3 56 135 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 135 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 135 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 135 196 (Polychromatic418967fa.accept_10_4_5_6_1_651
  54 135 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 135 196 (accept_3_3 53
  135 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 135 196
  (Polychromatic418967fa.accept_21_10_9_7_1_9857 52 135 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 135 196 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 135 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 135 196 (accept_3_3 50 135 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 135 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 135 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 135 196 (Polychromatic418967fa.accept_13_9_5_1_1_1382
  48 135 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 135 196 (accept_3_3 47
  135 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 135 196
  (Polychromatic418967fa.accept_16_14_7_4_1_3243 46 135 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 135 196 (Polychromatic418967fa.accept_13_6_5_1_1_834 45 135 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 135 196 (accept_3_3 44 135 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 135 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 135 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 135 196 (Polychromatic418967fa.accept_12_6_3_4_1_394
  42 135 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 135 196 (accept_3_3 41
  135 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 135 196
  (Polychromatic418967fa.accept_16_8_7_4_1_2217 40 135 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 135 196 (Polychromatic418967fa.accept_10_9_5_6_1_691 39 135 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 135 196 (accept_3_3 38 135 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 135 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 135 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 135 196
  (Polychromatic418967fa.accept_21_15_9_7_1_3780 36 135 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 135 196 (accept_3_3 35 135 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 135 196 (Polychromatic418967fa.accept_10_4_5_6_1_651 34 135 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 135 196 (Polychromatic418967fa.accept_18_15_9_16_1_6029 33 135 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 135 196 (accept_3_3 32 135 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 135 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 135 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 135 196
  (Polychromatic418967fa.accept_12_6_3_4_1_394 30 135 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 135 196 (accept_3_3 29 135 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 135 196 (Polychromatic418967fa.accept_11_6_3_9_1_906 28 135 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 135 196 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 135 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 135 196 (accept_3_3 26 135 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 135 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 135 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 135 196
  (Polychromatic418967fa.accept_10_4_5_6_1_651 24 135 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 135 196 (accept_3_3 23 135 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 135 196 (Polychromatic418967fa.accept_13_9_5_1_1_1382 22 135 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 135 196 (Polychromatic418967fa.accept_10_1_5_6_1_649 21 135 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 135 196 (accept_3_3 20 135 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 135 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 135 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 135 196
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 135 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 135 196 (accept_3_3 17 135 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 135 196 (Polychromatic418967fa.accept_13_3_5_1_1_2144 16 135 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 135 196 (Polychromatic418967fa.accept_18_15_9_16_1_6029 15 135 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 135 196 (accept_3_3 14 135 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 135 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 135 196
  (Polychromatic418967fa.accept_13_12_5_1_1_1383 12 135 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 135 196 (accept_3_3 11 135 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 135 196 (Polychromatic418967fa.accept_17_10_16_9_1_5127 10 135 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 135 196 (Polychromatic418967fa.accept_10_9_5_6_1_691 9 135 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 135 196 (accept_3_3 8 135 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 135 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 135 196
  (Polychromatic418967fa.accept_11_6_3_9_1_906 6 135 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 135 196 (accept_3_3 5 135 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  135 196 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 135 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 135 196 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 135 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 135 196 (accept_3_3 2 135 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 196 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 135 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135
  196)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 134 196 (Eq.refl Bool.true)
  (allA_of_3_1 63 134 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 64 133 196 (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 133 196 7 9 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 133 196 (accept_3_3 62 133 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 133 196 (Polychromatic418967fa.accept_22_17_1_20_1_9819 61 133 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 133 196 (Polychromatic418967fa.accept_16_12_5_4_1_3275 60 133 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 133 196 (accept_3_3 59 133 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 133 196 (Polychromatic418967fa.accept_10_8_3_6_1_685 58 133
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 133 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 133 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 133 196 7 8 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 133 196 (Polychromatic418967fa.accept_15_10_13_1_1_3698 55 133 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 133 196
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 54 133 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 133 196 (accept_3_3 53 133 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 133 196 (Polychromatic418967fa.accept_22_8_1_20_1_6508 52 133 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 133 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 133 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 133 196 (accept_3_3 50 133 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 49 133 196 7 7 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 133 196 (Polychromatic418967fa.accept_10_8_3_6_1_685 48 133 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 133 196 (accept_3_3 47 133 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 133 196 (Polychromatic418967fa.accept_12_10_1_4_1_392
  46 133 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 133 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 133 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 133 196 (accept_3_3 44 133 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 133 196 (Polychromatic418967fa.accept_11_10_1_9_1_2060 43 133 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 133 196 7 6 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 133 196 (accept_3_3 41 133 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 133 196 (Polychromatic418967fa.accept_15_10_13_1_1_3698 40 133 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 133 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 39
  133 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 133 196 (accept_3_3 38
  133 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 133 196
  (Polychromatic418967fa.accept_10_7_3_6_1_644 37 133 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 133 196 (Polychromatic418967fa.accept_22_14_1_20_1_11406 36 133 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 133 196 7 5 19 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 133 196
  (Polychromatic418967fa.accept_12_10_1_4_1_392 34 133 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 133 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 133 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 133 196 (accept_3_3 32 133 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 133 196 (Polychromatic418967fa.accept_13_5_3_1_1_1398 31 133 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 133 196
  (Polychromatic418967fa.accept_13_4_3_1_1_2898 30 133 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 133 196 (accept_3_3 29 133 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28
  133 196 7 4 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  27 133 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 133 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 133 196 (accept_3_3 26 133 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 133 196 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 133 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 133 196 (Polychromatic418967fa.accept_13_11_3_1_1_1397 24 133
  196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 133 196 (accept_3_3 23 133
  196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 133 196
  (Polychromatic418967fa.accept_12_10_1_4_1_392 22 133 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 133 196 7 3 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 133 196 (accept_3_3 20 133 196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 133 196 (Polychromatic418967fa.accept_10_9_3_6_1_686 19 133 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 133 196 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 133 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 133 196 (accept_3_3 17 133 196 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 133 196 (Polychromatic418967fa.accept_25_16_8_21_1_11412 16
  133 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 133 196
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 133 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 133 196 7 2 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 133 196 (Polychromatic418967fa.accept_23_13_18_12_1_8033 13 133 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 133 196
  (Polychromatic418967fa.accept_15_12_13_1_1_3695 12 133 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 133 196 (accept_3_3 11 133 196 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 133 196 (Polychromatic418967fa.accept_11_10_1_9_1_2060 10 133 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 133 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 133 196
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 133 196 (accept_3_3 8 133 196
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 133 196 7 1 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 133 196 (Polychromatic418967fa.accept_13_6_3_1_1_1413 6
  133 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 133 196 (accept_3_3 5 133
  196 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 133 196
  (Polychromatic418967fa.accept_13_4_3_1_1_2898 4 133 196 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 133 196 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 133 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 133 196 (accept_3_3 2 133 196 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 133 196 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 133 196 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 133
  196))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_196_segment_000)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


