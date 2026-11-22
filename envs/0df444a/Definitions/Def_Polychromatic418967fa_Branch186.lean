-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch186
-- name    : Polychromatic418967fa_Branch186
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:21:08.601777+00:00
-- url     : https://prove2.me/theorems/02562eda-6fb0-46bc-89f3-1e8e1ff52cdc
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch186_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_186 : allB 186 186 :=
  allB_succ' 2 185 186 (Eq.refl Bool.true) (allA_succ_of_accept 1 185 186 (accept_3_4 1 185 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 185 186)) (allB_succ' 3 184 186 (Eq.refl Bool.true) (allA_succ_of_gcd 2 184 186 2 1 92
  93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 184 186
  (Polychromatic418967fa.accept_9_1_4_6_1_5 1 184 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 184 186))) (allB_succ' 4 183 186 (Eq.refl Bool.true) (allA_succ_of_gcd 3 183 186 3 1 61 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 183 186
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 183 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 183 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 183 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 183 186)))) (allB_succ' 5 182 186 (Eq.refl Bool.true) (allA_succ_of_gcd 4
  182 186 2 2 91 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  3 182 186 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 182 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 182 186 2 1 91 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 182 186 (accept_3_4 1 182 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 182
  186))))) (allB_succ' 6 181 186 (Eq.refl Bool.true) (allA_succ_of_accept 5 181 186 (accept_3_5 5 181 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 181 186 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 181 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 181 186
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 181 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 181 186 (accept_3_5 2 181 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  181 186 (Polychromatic418967fa.accept_22_1_5_10_1_10706 1 181 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 181 186)))))) (allB_succ' 7 180 186 (Eq.refl Bool.true) (allA_succ_of_gcd 6 180 186 6 1 30 31
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 180 186
  (Polychromatic418967fa.accept_11_5_4_10_1_524 5 180 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 180 186 2 2 90 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 180 186 3 1 60 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 180 186 2 1 90 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 180 186 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 180 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 180 186))))))) (allB_succ' 8 179 186 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 179 186 (accept_3_4 7 179 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  179 186 (Polychromatic418967fa.accept_13_6_10_4_1_957 6 179 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 179 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 179 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 179 186 (accept_3_4 4 179 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 179 186 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 179 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 179 186
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 179 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 179 186 (accept_3_4 1 179 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 179
  186)))))))) (allB_succ' 9 178 186 (Eq.refl Bool.true) (allA_succ_of_gcd 8 178 186 2 4 89 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 178 186
  (Polychromatic418967fa.accept_13_7_9_4_1_918 7 178 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 178 186 2 3 89 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 178 186 (accept_3_5 5 178 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 178
  186 2 2 89 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  178 186 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 178 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 178 186 2 1 89 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 178 186 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 178 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 178 186))))))))) (allB_succ' 10 177 186 (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 177 186 3 3 59 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 177 186 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 177 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 177 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 177 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 177 186 3 2 59 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 177 186
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 177 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 177 186 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 177 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 177 186 3 1 59 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 177 186 (Polychromatic418967fa.accept_11_2_1_10_1_196 2 177 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 186
  (Polychromatic418967fa.accept_10_1_7_6_1_91 1 177 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 177 186)))))))))) (allB_succ' 11 176 186 (Eq.refl Bool.true) (allA_succ_of_gcd 10 176 186 2 5 88 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 176 186
  (Polychromatic418967fa.accept_12_9_8_6_1_466 9 176 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 176 186 2 4 88 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 176 186 (accept_3_4 7 176 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 176
  186 2 3 88 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  176 186 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 176 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 176 186 2 2 88 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 176 186 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 176 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 176 186 2 1 88 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 176 186 (accept_3_4 1 176 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 176 186))))))))))) (allB_succ' 12 175 186 (Eq.refl Bool.true) (allA_succ_of_accept 11
  175 186 (accept_3_5 11 175 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 175 186
  (Polychromatic418967fa.accept_9_1_4_6_1_5 10 175 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 175 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 175 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 175 186 (accept_3_5 8 175 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 175 186 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 175 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 175 186 (Polychromatic418967fa.accept_19_6_4_15_1_2432
  6 175 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 175 186 (accept_3_5 5
  175 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 175 186
  (Polychromatic418967fa.accept_10_4_5_6_1_651 4 175 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 175 186 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 175 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 175 186 (accept_3_5 2 175 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 175 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 175 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 175 186)))))))))))) (allB_succ' 13 174 186 (Eq.refl Bool.true)
  (allA_succ_of_gcd 12 174 186 6 2 29 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 174 186 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 174 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 174 186 2 5 87 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 174 186 3 3 58 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 174 186 2 4 87 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 174 186 (Polychromatic418967fa.accept_9_7_3_6_1_270 7
  174 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 174 186 6 1 29 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 174 186
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 174 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 174 186 2 2 87 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 174 186 3 1 58 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 174 186 2 1 87 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 174 186 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 174 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 174 186))))))))))))) (allB_succ' 14 173 186 (Eq.refl Bool.true)
  (allA_succ_of_accept 13 173 186 (accept_3_4 13 173 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 173 186 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 173 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 173 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 173 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 173 186 (accept_3_4 10 173 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 173 186 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 173 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 173 186
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 173 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 173 186 (accept_3_4 7 173 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  173 186 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 173 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 173 186 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 173 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 173 186 (accept_3_4 4 173 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 173 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 173 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 173 186
  (Polychromatic418967fa.accept_7_2_5_4_1_115 2 173 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 173 186 (accept_3_4 1 173 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 173
  186)))))))))))))) (allB_succ' 15 172 186 (Eq.refl Bool.true) (allA_succ_of_gcd 14 172 186 2 7 86 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 172 186
  (Polychromatic418967fa.accept_9_4_1_6_1_284 13 172 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 172 186 2 6 86 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 172 186 (accept_3_5 11 172 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  172 186 2 5 86 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 172 186 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 172 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 172 186 2 4 86 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 172 186 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 172 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 172 186 2 3 86 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 172 186 (accept_3_5 5 172 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 172 186 2 2 86 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 172 186 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 172 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 172 186 2 1 86 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 172 186
  (Polychromatic418967fa.accept_10_1_2_6_1_638 1 172 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 172 186))))))))))))))) (allB_succ' 16 171 186 (Eq.refl Bool.true) (allA_succ_of_gcd 15 171 186 3 5 57 62
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 171 186
  (Polychromatic418967fa.accept_12_2_3_6_1_112 14 171 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 171 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 171 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 171 186 3 4 57 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 171 186 (Polychromatic418967fa.accept_13_11_2_4_1_1590
  11 171 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 171 186
  (Polychromatic418967fa.accept_12_10_3_6_1_882 10 171 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 171 186 3 3 57 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 171 186 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 171 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 186 (Polychromatic418967fa.accept_10_7_1_6_1_673 7 171 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 171 186 3 2 57 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 171 186
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 171 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 171 186 (Polychromatic418967fa.accept_12_4_3_6_1_879 4 171 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 171 186 3 1 57 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 171 186 (Polychromatic418967fa.accept_10_2_1_6_1_634 2 171 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 186
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 171 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 171 186)))))))))))))))) (allB_succ' 17 170 186 (Eq.refl Bool.true) (allA_succ_of_gcd 16 170 186 2 8 85 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 170 186
  (Polychromatic418967fa.accept_11_4_5_10_1_926 15 170 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 170 186 2 7 85 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 170 186 (accept_3_4 13 170 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12
  170 186 2 6 85 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  11 170 186 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 170 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 170 186 2 5 85 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 170 186 (Polychromatic418967fa.accept_12_9_2_6_1_455 9 170 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 170 186 2 4 85 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 170 186 (accept_3_4 7 170 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 170 186 2 3 85 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 170 186 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 170 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 170 186 2 2 85 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 170 186
  (Polychromatic418967fa.accept_9_3_8_6_1_80 3 170 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 170 186 2 1 85 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 170 186 (accept_3_4 1 170 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 170
  186))))))))))))))))) (allB_succ' 18 169 186 (Eq.refl Bool.true) (allA_succ_of_accept 17 169 186 (accept_3_5 17 169 186
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 169 186 (Polychromatic418967fa.accept_11_5_4_10_1_524
  16 169 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 169 186
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 169 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 169 186 (accept_3_5 14 169 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 169 186 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 169 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 169 186 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 169 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 169 186 (accept_3_5 11 169 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 169 186 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 169 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 169 186
  (Polychromatic418967fa.accept_15_9_4_6_1_3075 9 169 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 169 186 (accept_3_5 8 169 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  169 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 169 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 169 186 (Polychromatic418967fa.accept_22_6_15_10_1_10705 6 169 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 169 186 (accept_3_5 5 169 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 169 186 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 169 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 169 186
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 169 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 169 186 (accept_3_5 2 169 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  169 186 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 169 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 169 186)))))))))))))))))) (allB_succ' 19 168 186 (Eq.refl Bool.true) (allA_succ_of_gcd 18 168
  186 6 3 28 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  168 186 (Polychromatic418967fa.accept_27_17_6_24_1_10704 17 168 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 168 186 2 8 84 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 15 168 186 3 5 56 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 14 168 186 2 7 84 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 168 186 (Polychromatic418967fa.accept_10_3_8_6_1_326 13 168 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 168 186 6 2 28 31 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 168 186
  (Polychromatic418967fa.accept_13_11_12_4_1_3945 11 168 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 168 186 2 5 84 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 9 168 186 3 3 56 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 8 168 186 2 4 84 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 7 168 186 (Polychromatic418967fa.accept_11_7_3_10_1_1461 7 168 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 168 186 6 1 28 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 168 186
  (Polychromatic418967fa.accept_13_5_12_4_1_449 5 168 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 168 186 2 2 84 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 168 186 3 1 56 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 168 186 2 1 84 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 168 186 (Polychromatic418967fa.accept_15_1_3_6_1_621 1 168 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 168 186))))))))))))))))))) (allB_succ' 20 167 186 (Eq.refl Bool.true)
  (allA_succ_of_accept 19 167 186 (accept_3_4 19 167 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 167 186 (Polychromatic418967fa.accept_26_18_11_4_1_10703 18 167 186 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 17 167 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 167 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 167 186 (accept_3_4 16 167 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 167 186 (Polychromatic418967fa.accept_13_2_11_4_1_445 15 167
  186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 167 186
  (Polychromatic418967fa.accept_16_14_7_10_1_898 14 167 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 167 186 (accept_3_4 13 167 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 167 186 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 167 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 167 186 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 167 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 167 186 (accept_3_4 10 167 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 167 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 167 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 167 186
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 167 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 167 186 (accept_3_4 7 167 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  167 186 (Polychromatic418967fa.accept_13_6_11_4_1_938 6 167 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 167 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 167 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 167 186 (accept_3_4 4 167 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 167 186 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 167 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 167 186
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 167 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 167 186 (accept_3_4 1 167 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 167
  186)))))))))))))))))))) (allB_succ' 21 166 186 (Eq.refl Bool.true) (allA_succ_of_gcd 20 166 186 2 10 83 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 166 186
  (Polychromatic418967fa.accept_9_1_4_6_1_5 19 166 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 166 186 2 9 83 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 166 186 (accept_3_5 17 166 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  166 186 2 8 83 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 166 186 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 166 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 166 186 2 7 83 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 166 186 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 166 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 166 186 2 6 83 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 166 186 (accept_3_5 11 166 186
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 166 186 2 5 83 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 166 186
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 166 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 166 186 2 4 83 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 166 186 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 166 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 166 186 2 3 83 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 166 186 (accept_3_5 5 166 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 166 186 2 2 83 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 166 186 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 166 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 166 186 2 1 83 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 166 186 (Polychromatic418967fa.accept_7_1_5_4_1_134 1
  166 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 166 186)))))))))))))))))))))
  (allB_succ' 22 165 186 (Eq.refl Bool.true) (allA_succ_of_gcd 21 165 186 3 7 55 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 165 186
  (Polychromatic418967fa.accept_9_2_3_6_1_88 20 165 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 165 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 165 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 165 186 3 6 55 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 165 186 (Polychromatic418967fa.accept_9_8_3_6_1_533 17
  165 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 165 186
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 165 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 165 186 3 5 55 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 165 186 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 165 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 165 186 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 165 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 165 186 3 4 55 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 165 186
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 165 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 165 186 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 165 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 165 186 3 3 55 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 165 186 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 165 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 186
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 165 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 165 186 3 2 55 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 165 186 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 165 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 165 186 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 165 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 165 186 3 1 55 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 165 186
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 165 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 165 186 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 165 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 165 186)))))))))))))))))))))) (allB_succ' 23 164 186 (Eq.refl Bool.true)
  (allA_succ_of_gcd 22 164 186 2 11 82 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 164 186 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 164 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 164 186 2 10 82 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 164 186 (accept_3_4 19 164 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 164 186 2 9 82 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 164 186 (Polychromatic418967fa.accept_9_8_2_6_1_875 17
  164 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 164 186 2 8 82 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 164 186
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 164 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 164 186 2 7 82 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 164 186 (accept_3_4 13 164 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12
  164 186 2 6 82 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  11 164 186 (Polychromatic418967fa.accept_13_11_8_4_1_3950 11 164 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 164 186 2 5 82 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 164 186 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 164 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 164 186 2 4 82 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 164 186 (accept_3_4 7 164 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 164 186 2 3 82 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 164 186 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 164 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 164 186 2 2 82 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 164 186
  (Polychromatic418967fa.accept_9_3_2_6_1_264 3 164 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 164 186 2 1 82 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 164 186 (accept_3_4 1 164 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 164
  186))))))))))))))))))))))) (allB_succ' 24 163 186 (Eq.refl Bool.true) (allA_succ_of_accept 23 163 186 (accept_3_5 23
  163 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 163 186
  (Polychromatic418967fa.accept_9_4_1_6_1_284 22 163 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 163 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 163 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 163 186 (accept_3_5 20 163 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 163 186 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 163 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 163 186 (Polychromatic418967fa.accept_10_8_3_6_1_685
  18 163 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 163 186 (accept_3_5 17
  163 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 163 186
  (Polychromatic418967fa.accept_9_7_1_6_1_261 16 163 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 163 186 (Polychromatic418967fa.accept_21_15_16_18_1_7529 15 163 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 163 186 (accept_3_5 14 163 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 163 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 163 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 163 186
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 163 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 163 186 (accept_3_5 11 163 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 163 186 (Polychromatic418967fa.accept_13_10_7_4_1_2262 10 163 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 163 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 163 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 163 186 (accept_3_5 8 163 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 163 186 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 163 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 163 186
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 163 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 163 186 (accept_3_5 5 163 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  163 186 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 163 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 163 186 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 163 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 163 186 (accept_3_5 2 163 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 163 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 163 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 163 186)))))))))))))))))))))))) (allB_succ' 25 162 186
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 162 186 6 4 27 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 162 186 (Polychromatic418967fa.accept_13_10_6_4_1_1583 23 162 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 162 186 2 11 81 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 162 186 3 7 54 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 162 186 2 10 81 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 162 186
  (Polychromatic418967fa.accept_7_5_1_4_1_122 19 162 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 162 186 6 3 27 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 162 186 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 162 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 162 186 2 8 81 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 162 186 3 5 54 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 162 186 2 7 81 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 162 186
  (Polychromatic418967fa.accept_17_13_9_16_1_3254 13 162 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 162 186 6 2 27 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 162 186 (Polychromatic418967fa.accept_10_1_2_6_1_638 11 162 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 162 186 2 5 81 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 162 186 3 3 54 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 162 186 2 4 81 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 162 186
  (Polychromatic418967fa.accept_13_7_6_4_1_933 7 162 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 162 186 6 1 27 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 162 186 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 162 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 162 186 2 2 81 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 162 186 3 1 54 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 162 186 2 1 81 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 162 186 (Polychromatic418967fa.accept_10_1_2_6_1_638 1 162 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162 186))))))))))))))))))))))))) (allB_succ' 26
  161 186 (Eq.refl Bool.true) (allA_succ_of_accept 25 161 186 (accept_3_4 25 161 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 161 186 (Polychromatic418967fa.accept_14_10_7_4_1_3453 24 161 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 161 186
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 161 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 161 186 (accept_3_4 22 161 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 161 186 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 161 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 161 186 (Polychromatic418967fa.accept_9_2_8_6_1_79 20 161 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 161 186 (accept_3_4 19 161 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 161 186 (Polychromatic418967fa.accept_15_3_11_6_1_3083 18 161 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 161 186
  (Polychromatic418967fa.accept_10_7_1_6_1_673 17 161 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 161 186 (accept_3_4 16 161 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 161 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 161 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 161 186 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 161 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 161 186 (accept_3_4 13 161 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 161 186 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 161 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 161 186
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 161 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 161 186 (accept_3_4 10 161 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  161 186 (Polychromatic418967fa.accept_13_9_5_4_1_1591 9 161 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 161 186 (Polychromatic418967fa.accept_22_8_7_10_1_10702 8 161 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 161 186 (accept_3_4 7 161 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 161 186 (Polychromatic418967fa.accept_13_6_5_4_1_3924 6 161 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 161 186
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 161 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 161 186 (accept_3_4 4 161 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  161 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 161 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 161 186 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 161 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 161 186 (accept_3_4 1 161 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 161 186)))))))))))))))))))))))))) (allB_succ' 27 160 186 (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 160 186 2 13 80 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 160 186 (Polychromatic418967fa.accept_17_8_7_16_1_9508 25 160 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 160 186 2 12 80 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 160 186 (accept_3_5 23 160 186
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 160 186 2 11 80 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 160 186
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 160 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 160 186 2 10 80 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 160 186 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 160 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 160 186 2 9 80 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 160 186 (accept_3_5 17 160 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 160 186 2 8 80 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 160 186 (Polychromatic418967fa.accept_12_3_4_6_1_434
  15 160 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 160 186 2 7 80 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 160 186
  (Polychromatic418967fa.accept_9_4_7_6_1_255 13 160 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 160 186 2 6 80 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 160 186 (accept_3_5 11 160 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  160 186 2 5 80 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 160 186 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 160 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 160 186 2 4 80 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 160 186 (Polychromatic418967fa.accept_19_7_8_15_1_2448 7 160 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 160 186 2 3 80 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 160 186 (accept_3_5 5 160 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 160 186 2 2 80 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 160 186 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 160 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 160 186 2 1 80 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 160 186
  (Polychromatic418967fa.accept_9_1_7_6_1_75 1 160 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 160 186))))))))))))))))))))))))))) (allB_succ' 28 159 186 (Eq.refl Bool.true) (allA_succ_of_gcd 27 159 186 3
  9 53 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 159
  186 (Polychromatic418967fa.accept_11_4_5_10_1_926 26 159 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 159 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 159 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 159 186 3 8 53 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 159 186
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 159 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 159 186 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 159 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 159 186 3 7 53 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 159 186 (Polychromatic418967fa.accept_7_6_5_4_1_297 20
  159 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 159 186
  (Polychromatic418967fa.accept_15_4_9_6_1_627 19 159 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 159 186 3 6 53 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 159 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 159 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 159 186 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 159 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 159 186 3 5 53 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 159 186
  (Polychromatic418967fa.accept_12_2_3_6_1_112 14 159 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 159 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 159 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 159 186 3 4 53 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 159 186 (Polychromatic418967fa.accept_15_11_9_6_1_1321
  11 159 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 159 186
  (Polychromatic418967fa.accept_12_10_3_6_1_882 10 159 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 159 186 3 3 53 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 159 186 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 159 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 186 (Polychromatic418967fa.accept_13_7_3_4_1_459 7 159 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 159 186 3 2 53 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 159 186
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 159 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 159 186 (Polychromatic418967fa.accept_11_4_5_10_1_926 4 159 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 159 186 3 1 53 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 159 186 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 159 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 186
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 159 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 159 186)))))))))))))))))))))))))))) (allB_succ' 29 158 186 (Eq.refl Bool.true) (allA_succ_of_gcd 28 158 186
  2 14 79 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 158
  186 (Polychromatic418967fa.accept_11_5_4_10_1_524 27 158 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 158 186 2 13 79 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 158 186 (accept_3_4 25 158 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 158 186 2 12 79 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 158 186 (Polychromatic418967fa.accept_10_3_8_6_1_326 23 158 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 158 186 2 11 79 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 158 186
  (Polychromatic418967fa.accept_9_3_5_6_1_253 21 158 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 158 186 2 10 79 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 158 186 (accept_3_4 19 158 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 158 186 2 9 79 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 158 186 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 158 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 158 186 2 8 79 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 158 186 (Polychromatic418967fa.accept_12_3_2_6_1_138
  15 158 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 158 186 2 7 79 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 158 186
  (accept_3_4 13 158 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 158 186 2 6 79 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 158 186
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 158 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 158 186 2 5 79 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 158 186 (Polychromatic418967fa.accept_12_9_2_6_1_455 9 158 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 158 186 2 4 79 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 158 186 (accept_3_4 7 158 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 158 186 2 3 79 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 158 186 (Polychromatic418967fa.accept_11_5_4_10_1_524 5 158 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 158 186 2 2 79 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 158 186 (Polychromatic418967fa.accept_9_3_5_6_1_253 3
  158 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 158 186 2 1 79 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 158 186 (accept_3_4 1
  158 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158 186))))))))))))))))))))))))))))) (allB_succ' 30 157 186
  (Eq.refl Bool.true) (allA_succ_of_accept 29 157 186 (accept_3_5 29 157 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 157 186 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 157 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 157 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 157 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 157 186 (accept_3_5 26 157 186
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 157 186 (Polychromatic418967fa.accept_9_7_4_6_1_273
  25 157 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 157 186
  (Polychromatic418967fa.accept_21_3_10_18_1_7631 24 157 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 157 186 (accept_3_5 23 157 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 157 186 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 157 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 157 186 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 157 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 157 186 (accept_3_5 20 157 186
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 157 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 19
  157 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 157 186
  (Polychromatic418967fa.accept_11_7_3_10_1_1461 18 157 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 157 186 (accept_3_5 17 157 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 157 186 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 157 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 157 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 157 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 157 186 (accept_3_5 14 157 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 157 186 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 157 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 157 186
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 157 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 157 186 (accept_3_5 11 157 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 157 186 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 157 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 157 186 (Polychromatic418967fa.accept_18_9_13_6_1_877 9 157 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 157 186 (accept_3_5 8 157 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 157 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 157 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 157 186
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 157 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 157 186 (accept_3_5 5 157 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  157 186 (Polychromatic418967fa.accept_19_4_5_15_1_2437 4 157 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 157 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 157 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 157 186 (accept_3_5 2 157 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 157 186 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 157 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 157 186)))))))))))))))))))))))))))))) (allB_succ' 31 156
  186 (Eq.refl Bool.true) (allA_succ_of_gcd 30 156 186 6 5 26 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 156 186 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 156 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 156 186 2 14 78 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 156 186 3 9 52 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 156 186 2 13 78 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 156 186
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 156 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 156 186 6 4 26 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 156 186 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 156 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 156 186 2 11 78 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 156 186 3 7 52 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 156 186 2 10 78 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 156 186
  (Polychromatic418967fa.accept_7_5_2_4_1_126 19 156 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 156 186 6 3 26 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 156 186 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 156 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 156 186 2 8 78 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 156 186 3 5 52 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 156 186 2 7 78 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 156 186 (Polychromatic418967fa.accept_7_6_2_4_1_291 13
  156 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 156 186 6 2 26 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 156 186
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 156 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 156 186 2 5 78 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 156 186 3 3 52 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 156 186 2 4 78 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 156 186 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 156 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 156 186 6 1 26 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 156 186 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 156 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 156 186 2 2 78 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 156 186 3 1 52 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 156 186 2 1 78 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 156 186
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 156 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 156 186))))))))))))))))))))))))))))))) (allB_succ' 32 155 186 (Eq.refl Bool.true) (allA_succ_of_gcd 31 155
  186 31 1 5 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 30
  155 186 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 155 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 155 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 155 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 155 186 (accept_3_4 28 155 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 155 186 (Polychromatic418967fa.accept_15_12_5_6_1_2148 27 155 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 155 186
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 155 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 155 186 (accept_3_4 25 155 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 155 186 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 155 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 155 186 (Polychromatic418967fa.accept_9_5_2_6_1_265 23 155 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 155 186 (accept_3_4 22 155 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 155 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 155 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 155 186
  (Polychromatic418967fa.accept_11_9_1_10_1_920 20 155 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 155 186 (accept_3_4 19 155 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 155 186 (Polychromatic418967fa.accept_13_5_12_4_1_449 18 155 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 155 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 155 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 155 186 (accept_3_4 16 155 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 155 186 (Polychromatic418967fa.accept_13_2_12_4_1_943 15 155 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 155 186
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 155 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 155 186 (accept_3_4 13 155 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 155 186 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 155 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 155 186 (Polychromatic418967fa.accept_10_1_5_6_1_649 11 155 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 155 186 (accept_3_4 10 155 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 155 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 155 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 155 186
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 155 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 155 186 (accept_3_4 7 155 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  155 186 (Polychromatic418967fa.accept_23_6_17_2_1_10701 6 155 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 155 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 155 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 155 186 (accept_3_4 4 155 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 155 186 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 155 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 155 186
  (Polychromatic418967fa.accept_11_2_1_10_1_196 2 155 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 155 186 (accept_3_4 1 155 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 155
  186)))))))))))))))))))))))))))))))) (allB_succ' 33 154 186 (Eq.refl Bool.true) (allA_succ_of_gcd 32 154 186 2 16 77 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 154 186
  (Polychromatic418967fa.accept_9_4_1_6_1_284 31 154 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 154 186 2 15 77 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 154 186 (accept_3_5 29 154 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 154 186 2 14 77 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 154 186 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 154 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 154 186 2 13 77 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 154 186
  (Polychromatic418967fa.accept_9_7_1_6_1_261 25 154 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 154 186 2 12 77 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 154 186 (accept_3_5 23 154 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 154 186 2 11 77 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 154 186 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 154 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 154 186 2 10 77 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 154 186
  (Polychromatic418967fa.accept_13_6_11_4_1_938 19 154 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 154 186 2 9 77 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 154 186 (accept_3_5 17 154 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  154 186 2 8 77 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 154 186 (Polychromatic418967fa.accept_10_5_4_6_1_319 15 154 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 154 186 2 7 77 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 154 186 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 154 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 154 186 2 6 77 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 154 186 (accept_3_5 11 154 186
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 154 186 2 5 77 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 154 186
  (Polychromatic418967fa.accept_12_9_10_6_1_872 9 154 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 154 186 2 4 77 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 154 186 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 154 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 154 186 2 3 77 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 154 186 (accept_3_5 5 154 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 154 186 2 2 77 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 154 186 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 154 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 154 186 2 1 77 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 154 186 (Polychromatic418967fa.accept_19_1_2_15_1_3684
  1 154 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 154
  186))))))))))))))))))))))))))))))))) (allB_succ' 34 153 186 (Eq.refl Bool.true) (allA_succ_of_gcd 33 153 186 3 11 51
  62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 153 186
  (Polychromatic418967fa.accept_12_8_9_6_1_127 32 153 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 153 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 153 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 153 186 3 10 51 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 153 186 (Polychromatic418967fa.accept_10_9_3_6_1_686
  29 153 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 153 186
  (Polychromatic418967fa.accept_10_8_3_6_1_685 28 153 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 153 186 3 9 51 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 153 186 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 153 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 153 186 (Polychromatic418967fa.accept_15_10_3_6_1_3042 25 153
  186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 153 186 3 8 51 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 153 186
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 153 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 153 186 (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 153 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 153 186 3 7 51 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 153 186 (Polychromatic418967fa.accept_12_8_9_6_1_127
  20 153 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 186
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 153 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 153 186 3 6 51 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 153 186 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 153 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 153 186 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 153 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 153 186 3 5 51 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 153 186
  (Polychromatic418967fa.accept_12_2_9_6_1_439 14 153 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 153 186 (Polychromatic418967fa.accept_18_13_9_6_1_4024 13 153 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 153 186 3 4 51 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 153 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 11
  153 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 153 186
  (Polychromatic418967fa.accept_7_3_6_4_1_30 10 153 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 153 186 3 3 51 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 153 186 (Polychromatic418967fa.accept_10_8_3_6_1_685 8 153 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 153 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 153 186 3 2 51 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 153 186
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 153 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 153 186 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 153 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 153 186 3 1 51 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 153 186 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 153 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 186
  (Polychromatic418967fa.accept_13_1_10_4_1_954 1 153 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 153 186)))))))))))))))))))))))))))))))))) (allB_succ' 35 152 186 (Eq.refl Bool.true) (allA_succ_of_gcd 34
  152 186 2 17 76 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 152 186 (Polychromatic418967fa.accept_12_9_8_6_1_466 33 152 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 152 186 2 16 76 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 152 186 (accept_3_4 31 152 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 152 186 2 15 76 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 152 186 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 152 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 152 186 2 14 76 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 152 186
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 152 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 152 186 2 13 76 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 152 186 (accept_3_4 25 152 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 152 186 2 12 76 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 152 186 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 152 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 152 186 2 11 76 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 152 186
  (Polychromatic418967fa.accept_9_3_8_6_1_80 21 152 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 152 186 2 10 76 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 152 186 (accept_3_4 19 152 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 152 186 2 9 76 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 152 186 (Polychromatic418967fa.accept_20_17_12_6_1_6171 17 152 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 152 186 2 8 76 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 152 186
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 152 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 152 186 2 7 76 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 152 186 (accept_3_4 13 152 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12
  152 186 2 6 76 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  11 152 186 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 152 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 152 186 2 5 76 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 152 186 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 152 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 152 186 2 4 76 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 152 186 (accept_3_4 7 152 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 152 186 2 3 76 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 152 186 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 152 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 152 186 2 2 76 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 152 186
  (Polychromatic418967fa.accept_9_3_8_6_1_80 3 152 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 152 186 2 1 76 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 152 186 (accept_3_4 1 152 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152
  186))))))))))))))))))))))))))))))))))) (allB_succ' 36 151 186 (Eq.refl Bool.true) (allA_succ_of_accept 35 151 186
  (accept_3_5 35 151 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 151 186
  (Polychromatic418967fa.accept_20_14_11_6_1_6264 34 151 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 151 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 151 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 151 186 (accept_3_5 32 151 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 151 186 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 151 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 151 186
  (Polychromatic418967fa.accept_9_3_7_6_1_76 30 151 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 151 186 (accept_3_5 29 151 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 151 186 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 151 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 151 186 (Polychromatic418967fa.accept_10_7_1_6_1_673 27 151 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 151 186 (accept_3_5 26 151 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 151 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 151 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 151 186
  (Polychromatic418967fa.accept_13_11_8_4_1_3950 24 151 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 151 186 (accept_3_5 23 151 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 151 186 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 151 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 151 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 151 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 151 186 (accept_3_5 20 151 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 151 186 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 151 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 151 186
  (Polychromatic418967fa.accept_15_3_1_6_1_206 18 151 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 151 186 (accept_3_5 17 151 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 151 186 (Polychromatic418967fa.accept_19_16_18_15_1_3681 16 151 186 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 151 186 (Polychromatic418967fa.accept_10_5_1_6_1_672 15 151 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 151 186 (accept_3_5 14 151 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 151 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 151 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 151 186
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 151 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 151 186 (accept_3_5 11 151 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 151 186 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 151 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 151 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 151 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 151 186 (accept_3_5 8 151 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 151 186 (Polychromatic418967fa.accept_10_7_1_6_1_673 7 151 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 151 186
  (Polychromatic418967fa.accept_21_6_4_18_1_9164 6 151 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 151 186 (accept_3_5 5 151 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  151 186 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 151 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 151 186 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 151 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 151 186 (accept_3_5 2 151 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 151 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 151 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 151 186)))))))))))))))))))))))))))))))))))) (allB_succ'
  37 150 186 (Eq.refl Bool.true) (allA_succ_of_gcd 36 150 186 6 6 25 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 150 186 (Polychromatic418967fa.accept_13_9_7_4_1_953 35 150 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 150 186 2 17 75 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 150 186 3 11 50 62
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 150 186 2 16 75
  93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 150 186
  (Polychromatic418967fa.accept_19_12_17_15_1_6460 31 150 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 150 186 6 5 25 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 150 186 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 150 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 150 186 2 14 75 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 150 186 3 9 50 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 150 186 2 13 75 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 150 186
  (Polychromatic418967fa.accept_11_3_7_10_1_180 25 150 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 150 186 6 4 25 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 150 186 (Polychromatic418967fa.accept_13_10_7_4_1_2262 23 150 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 150 186 2 11 75 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 150 186 3 7 50 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 150 186 2 10 75 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 150 186
  (Polychromatic418967fa.accept_13_6_7_4_1_2264 19 150 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 150 186 6 3 25 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 150 186 (Polychromatic418967fa.accept_21_17_3_18_1_7549 17 150 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 150 186 2 8 75 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 150 186 3 5 50 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 150 186 2 7 75 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 150 186
  (Polychromatic418967fa.accept_7_6_3_4_1_294 13 150 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 150 186 6 2 25 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 150 186 (Polychromatic418967fa.accept_13_11_7_4_1_1561 11 150 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 150 186 2 5 75 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 150 186 3 3 50 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 150 186 2 4 75 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 150 186 (Polychromatic418967fa.accept_14_7_10_4_1_130 7
  150 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 150 186 6 1 25 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 150 186
  (Polychromatic418967fa.accept_19_5_17_15_1_9225 5 150 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 150 186 2 2 75 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 150 186 3 1 50 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 150 186 2 1 75 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 150 186 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 150 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 150 186))))))))))))))))))))))))))))))))))))) (allB_succ' 38 149 186 (Eq.refl
  Bool.true) (allA_succ_of_accept 37 149 186 (accept_3_4 37 149 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 149 186 (Polychromatic418967fa.accept_13_10_6_4_1_1583 36 149 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 149 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 149 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 149 186 (accept_3_4 34 149 186
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 149 186 (Polychromatic418967fa.accept_7_5_2_4_1_126
  33 149 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 149 186
  (Polychromatic418967fa.accept_19_13_16_15_1_3781 32 149 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 149 186 (accept_3_4 31 149 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 149 186 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 149 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 149 186 (Polychromatic418967fa.accept_9_2_5_6_1_536 29 149 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 149 186 (accept_3_4 28 149 186
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 149 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 27
  149 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 149 186
  (Polychromatic418967fa.accept_7_5_2_4_1_126 26 149 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 149 186 (accept_3_4 25 149 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 149 186 (Polychromatic418967fa.accept_13_11_6_4_1_3121 24 149 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 149 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 149 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 149 186 (accept_3_4 22 149 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 149 186 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 149 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 149 186
  (Polychromatic418967fa.accept_7_6_2_4_1_291 20 149 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 149 186 (accept_3_4 19 149 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 149 186 (Polychromatic418967fa.accept_13_5_6_4_1_1582 18 149 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 149 186 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 149 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 149 186 (accept_3_4 16 149 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 149 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 149 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 149 186
  (Polychromatic418967fa.accept_16_14_5_10_1_3622 14 149 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 149 186 (accept_3_4 13 149 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 149 186 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 149 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 149 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 149 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 149 186 (accept_3_4 10 149 186
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 149 186 (Polychromatic418967fa.accept_13_9_6_4_1_2243
  9 149 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 149 186
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 149 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 149 186 (accept_3_4 7 149 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  149 186 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 149 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 149 186 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 149 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 149 186 (accept_3_4 4 149 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 149 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 149 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 149 186
  (Polychromatic418967fa.accept_9_2_5_6_1_536 2 149 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 149 186 (accept_3_4 1 149 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 149
  186)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 148 186 (Eq.refl Bool.true) (allA_succ_of_gcd 38 148 186 2 19
  74 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 148 186
  (Polychromatic418967fa.accept_9_1_4_6_1_5 37 148 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 148 186 2 18 74 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 148 186 (accept_3_5 35 148 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 148 186 2 17 74 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 148 186 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 148 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 148 186 2 16 74 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 148 186
  (Polychromatic418967fa.accept_7_3_1_4_1_121 31 148 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 148 186 2 15 74 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 148 186 (accept_3_5 29 148 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 148 186 2 14 74 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 148 186 (Polychromatic418967fa.accept_12_3_4_6_1_434 27 148 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 148 186 2 13 74 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 148 186
  (Polychromatic418967fa.accept_9_7_4_6_1_273 25 148 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 148 186 2 12 74 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 148 186 (accept_3_5 23 148 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 148 186 2 11 74 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 148 186 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 148 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 148 186 2 10 74 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 148 186
  (Polychromatic418967fa.accept_7_5_1_4_1_122 19 148 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 148 186 2 9 74 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 148 186 (accept_3_5 17 148 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  148 186 2 8 74 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 148 186 (Polychromatic418967fa.accept_11_4_5_10_1_926 15 148 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 148 186 2 7 74 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 148 186 (Polychromatic418967fa.accept_10_3_8_6_1_326 13 148 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 148 186 2 6 74 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 148 186 (accept_3_5 11 148 186
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 148 186 2 5 74 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 148 186
  (Polychromatic418967fa.accept_12_9_4_6_1_460 9 148 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 148 186 2 4 74 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 148 186 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 148 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 148 186 2 3 74 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 148 186 (accept_3_5 5 148 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 148 186 2 2 74 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 148 186 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 148 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 148 186 2 1 74 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 148 186 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 148
  186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 148
  186))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 147 186 (Eq.refl Bool.true) (allA_succ_of_gcd 39 147 186 3
  13 49 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 147
  186 (Polychromatic418967fa.accept_9_2_3_6_1_88 38 147 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 147 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 147 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 147 186 3 12 49 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 147 186 (Polychromatic418967fa.accept_9_8_3_6_1_533 35
  147 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 147 186
  (Polychromatic418967fa.accept_9_7_3_6_1_270 34 147 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 147 186 3 11 49 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 147 186 (Polychromatic418967fa.accept_9_5_3_6_1_269 32 147 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 147 186 (Polychromatic418967fa.accept_9_4_3_6_1_532
  31 147 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 147 186 3 10 49 62
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 147 186
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 147 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 147 186 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 147 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 147 186 3 9 49 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 147 186 (Polychromatic418967fa.accept_9_8_3_6_1_533 26
  147 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 147 186
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 147 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 147 186 3 8 49 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 147 186 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 147 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 147 186 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 147 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 147 186 3 7 49 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 147 186
  (Polychromatic418967fa.accept_9_2_3_6_1_88 20 147 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 147 186 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 147 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 147 186 3 6 49 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 147 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 17
  147 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 147 186
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 147 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 147 186 3 5 49 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 147 186 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 147 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 147 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 147 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 147 186 3 4 49 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 147 186
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 147 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 147 186 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 147 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 147 186 3 3 49 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 147 186 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 147 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 186
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 147 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 147 186 3 2 49 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 147 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 147 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 147 186 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 147 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 147 186 3 1 49 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 147 186
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 147 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 147 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 147 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 147 186)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 146 186
  (Eq.refl Bool.true) (allA_succ_of_gcd 40 146 186 2 20 73 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 146 186 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 146 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 146 186 2 19 73 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 146 186 (accept_3_4 37
  146 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 146 186 2 18 73 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 146 186
  (Polychromatic418967fa.accept_9_8_2_6_1_875 35 146 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 146 186 2 17 73 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 146 186 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 146 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 146 186 2 16 73 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 146 186 (accept_3_4 31 146 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 146 186 2 15 73 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 146 186 (Polychromatic418967fa.accept_11_7_3_10_1_1461
  29 146 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 146 186 2 14 73 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 146 186
  (Polychromatic418967fa.accept_12_3_2_6_1_138 27 146 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 146 186 2 13 73 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 146 186 (accept_3_4 25 146 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 146 186 2 12 73 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 146 186 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 146 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 146 186 2 11 73 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 146 186
  (Polychromatic418967fa.accept_9_3_2_6_1_264 21 146 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 146 186 2 10 73 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 146 186 (accept_3_4 19 146 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 146 186 2 9 73 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 146 186 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 146 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 146 186 2 8 73 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 146 186 (Polychromatic418967fa.accept_12_3_2_6_1_138
  15 146 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 146 186 2 7 73 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 146 186
  (accept_3_4 13 146 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 146 186 2 6 73 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 146 186
  (Polychromatic418967fa.accept_21_11_20_18_1_7656 11 146 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 146 186 2 5 73 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 146 186 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 146 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 146 186 2 4 73 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 146 186 (accept_3_4 7 146 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 146 186 2 3 73 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 146 186 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 146 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 146 186 2 2 73 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 146 186
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 146 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 146 186 2 1 73 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 146 186 (accept_3_4 1 146 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146
  186))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 145 186 (Eq.refl Bool.true) (allA_succ_of_accept 41 145
  186 (accept_3_5 41 145 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 145 186
  (Polychromatic418967fa.accept_9_4_1_6_1_284 40 145 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 145 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 145 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 145 186 (accept_3_5 38 145 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 145 186 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 145 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 145 186 (Polychromatic418967fa.accept_7_1_5_4_1_134
  36 145 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 145 186 (accept_3_5 35
  145 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 145 186
  (Polychromatic418967fa.accept_7_6_5_4_1_297 34 145 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 145 186 (Polychromatic418967fa.accept_15_3_10_6_1_632 33 145 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 145 186 (accept_3_5 32 145 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 145 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 145 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 145 186 (Polychromatic418967fa.accept_7_2_5_4_1_115
  30 145 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 145 186 (accept_3_5 29
  145 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 145 186
  (Polychromatic418967fa.accept_21_7_19_18_1_7540 28 145 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 145 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 145 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 145 186 (accept_3_5 26 145 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 145 186 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 145 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 145 186
  (Polychromatic418967fa.accept_10_4_5_6_1_651 24 145 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 145 186 (accept_3_5 23 145 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 145 186 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 145 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 145 186 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 145 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 145 186 (accept_3_5 20 145 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 145 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 145 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 145 186
  (Polychromatic418967fa.accept_13_5_2_4_1_3955 18 145 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 145 186 (accept_3_5 17 145 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 145 186 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 145 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 145 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 145 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 145 186 (accept_3_5 14 145 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 145 186 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 145 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 145 186
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 145 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 145 186 (accept_3_5 11 145 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 145 186 (Polychromatic418967fa.accept_17_10_9_16_1_5607 10 145 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 145 186 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 145 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 145 186 (accept_3_5 8 145 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 145 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 145 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 145 186
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 145 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 145 186 (accept_3_5 5 145 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  145 186 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 145 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 145 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 145 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 145 186 (accept_3_5 2 145 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 145 186 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 145 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 145 186))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 43 144 186 (Eq.refl Bool.true) (allA_succ_of_gcd 42 144 186 6 7 24 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 144 186
  (Polychromatic418967fa.accept_15_11_9_6_1_1321 41 144 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 144 186 2 20 72 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 144 186 3 13 48 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 144 186 2 19 72 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 144 186 (Polychromatic418967fa.accept_22_15_12_10_1_10700 37
  144 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 144 186 6 6 24 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 144 186
  (Polychromatic418967fa.accept_10_5_4_6_1_319 35 144 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 144 186 2 17 72 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 144 186 3 11 48 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 144 186 2 16 72 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 144 186 (Polychromatic418967fa.accept_11_9_1_10_1_920 31 144
  186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 144 186 6 5 24 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 144 186
  (Polychromatic418967fa.accept_13_3_1_4_1_945 29 144 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 144 186 2 14 72 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 27 144 186 3 9 48 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 144 186 2 13 72 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 144 186 (Polychromatic418967fa.accept_10_5_4_6_1_319 25 144 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 144 186 6 4 24 31 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 144 186
  (Polychromatic418967fa.accept_13_10_1_4_1_3103 23 144 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 144 186 2 11 72 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 144 186 3 7 48 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 144 186 2 10 72 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 144 186 (Polychromatic418967fa.accept_15_4_9_6_1_627 19 144 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 144 186 6 3 24 31 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 144 186
  (Polychromatic418967fa.accept_23_17_6_2_1_2369 17 144 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 144 186 2 8 72 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 144 186 3 5 48 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 144 186 2 7 72 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 144 186 (Polychromatic418967fa.accept_11_2_1_10_1_196 13 144 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 144 186 6 2 24 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 144 186 (Polychromatic418967fa.accept_15_11_9_6_1_1321
  11 144 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 144 186 2 5 72 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 144 186 3 3 48 62
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 144 186 2 4 72 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 144 186
  (Polychromatic418967fa.accept_17_7_8_16_1_6966 7 144 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 144 186 6 1 24 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 144 186 (Polychromatic418967fa.accept_10_5_4_6_1_319 5 144 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 144 186 2 2 72 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 144 186 3 1 48 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 144 186 2 1 72 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 144 186 (Polychromatic418967fa.accept_15_1_9_6_1_1323 1 144 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144
  186))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 143 186 (Eq.refl Bool.true) (allA_succ_of_accept 43 143
  186 (accept_3_4 43 143 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 143 186
  (Polychromatic418967fa.accept_17_8_7_16_1_9508 42 143 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 143 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 143 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 143 186 (accept_3_4 40 143 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 143 186 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 143 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 143 186 (Polychromatic418967fa.accept_9_2_8_6_1_79 38
  143 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 143 186 (accept_3_4 37
  143 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 143 186
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 143 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 143 186 (Polychromatic418967fa.accept_14_7_3_4_1_1816 35 143 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 143 186 (accept_3_4 34 143 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 143 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 143 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 143 186 (Polychromatic418967fa.accept_9_5_8_6_1_281
  32 143 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 143 186 (accept_3_4 31
  143 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 143 186
  (Polychromatic418967fa.accept_9_3_8_6_1_80 30 143 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 143 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 143 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 143 186 (accept_3_4 28 143 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 143 186 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 143 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 143 186
  (Polychromatic418967fa.accept_22_4_11_10_1_10691 26 143 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 143 186 (accept_3_4 25 143 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 143 186 (Polychromatic418967fa.accept_19_5_10_15_1_5076 24 143 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 143 186 (Polychromatic418967fa.accept_9_5_8_6_1_281
  23 143 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 143 186 (accept_3_4 22
  143 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 143 186
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 143 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 143 186 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 143 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 143 186 (accept_3_4 19 143 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 143 186 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 143 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 143 186
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 143 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 143 186 (accept_3_4 16 143 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 143 186 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 143 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 143 186 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 143 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 143 186 (accept_3_4 13 143 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 143 186 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 143 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 143 186
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 143 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 143 186 (accept_3_4 10 143 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  143 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 143 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 143 186 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 143 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 143 186 (accept_3_4 7 143 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 143 186 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 143 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 143 186
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 143 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 143 186 (accept_3_4 4 143 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  143 186 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 143 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 143 186 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 143 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 143 186 (accept_3_4 1 143 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 143 186)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 142 186 (Eq.refl
  Bool.true) (allA_succ_of_gcd 44 142 186 2 22 71 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 142 186 (Polychromatic418967fa.accept_15_13_7_6_1_682 43 142 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 142 186 2 21 71 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 142 186 (accept_3_5 41 142 186
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 142 186 2 20 71 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 142 186
  (Polychromatic418967fa.accept_9_3_7_6_1_76 39 142 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 142 186 2 19 71 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 142 186 (Polychromatic418967fa.accept_9_1_7_6_1_75 37 142 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 142 186 2 18 71 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 142 186 (accept_3_5 35 142 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 142 186 2 17 71 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 142 186 (Polychromatic418967fa.accept_7_5_2_4_1_126 33
  142 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 142 186 2 16 71 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 142 186
  (Polychromatic418967fa.accept_9_4_7_6_1_255 31 142 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 142 186 2 15 71 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 142 186 (accept_3_5 29 142 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 142 186 2 14 71 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 142 186 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 142 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 142 186 2 13 71 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 142 186
  (Polychromatic418967fa.accept_19_6_9_15_1_3694 25 142 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 142 186 2 12 71 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 142 186 (accept_3_5 23 142 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 142 186 2 11 71 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 142 186 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 142 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 142 186 2 10 71 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 142 186
  (Polychromatic418967fa.accept_7_5_2_4_1_126 19 142 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 142 186 2 9 71 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 142 186 (accept_3_5 17 142 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  142 186 2 8 71 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 142 186 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 142 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 142 186 2 7 71 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 142 186 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 142 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 142 186 2 6 71 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 142 186 (accept_3_5 11 142 186
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 142 186 2 5 71 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 142 186
  (Polychromatic418967fa.accept_12_9_10_6_1_872 9 142 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 142 186 2 4 71 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 142 186 (Polychromatic418967fa.accept_13_7_12_4_1_450 7 142 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 142 186 2 3 71 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 142 186 (accept_3_5 5 142 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 142 186 2 2 71 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 142 186 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 142 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 142 186 2 1 71 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 142 186 (Polychromatic418967fa.accept_9_1_7_6_1_75 1
  142 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142
  186))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 141 186 (Eq.refl Bool.true) (allA_succ_of_gcd 45 141
  186 3 15 47 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44
  141 186 (Polychromatic418967fa.accept_12_8_9_6_1_127 44 141 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 141 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 141 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 141 186 3 14 47 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 141 186
  (Polychromatic418967fa.accept_11_8_9_10_1_503 41 141 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 141 186 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 141 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 141 186 3 13 47 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 141 186 (Polychromatic418967fa.accept_7_3_1_4_1_121 38
  141 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 141 186
  (Polychromatic418967fa.accept_10_7_1_6_1_673 37 141 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 141 186 3 12 47 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 141 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 141 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 141 186 (Polychromatic418967fa.accept_11_1_9_10_1_184
  34 141 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 141 186 3 11 47 62
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 141 186
  (Polychromatic418967fa.accept_10_2_1_6_1_634 32 141 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 141 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 141 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 141 186 3 10 47 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 141 186
  (Polychromatic418967fa.accept_18_11_15_6_1_2832 29 141 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 141 186 (Polychromatic418967fa.accept_12_4_9_6_1_440 28 141 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 141 186 3 9 47 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 141 186
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 141 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 141 186 (Polychromatic418967fa.accept_10_5_1_6_1_672 25 141 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 141 186 3 8 47 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 141 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 23
  141 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 141 186
  (Polychromatic418967fa.accept_10_2_1_6_1_634 22 141 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 141 186 3 7 47 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 141 186 (Polychromatic418967fa.accept_12_8_9_6_1_127 20 141 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 141 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 141 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 141 186 3 6 47 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 141 186
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 141 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 141 186 (Polychromatic418967fa.accept_12_4_9_6_1_440 16 141 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 141 186 3 5 47 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 141 186 (Polychromatic418967fa.accept_12_2_9_6_1_439
  14 141 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 186
  (Polychromatic418967fa.accept_21_13_15_18_1_9124 13 141 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 141 186 3 4 47 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 141 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 141 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 141 186
  (Polychromatic418967fa.accept_7_3_1_4_1_121 10 141 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 141 186 3 3 47 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 141 186 (Polychromatic418967fa.accept_11_8_9_10_1_503 8 141 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 141 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 141 186 3 2 47 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 141 186
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 141 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 141 186 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 141 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 141 186 3 1 47 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 141 186 (Polychromatic418967fa.accept_10_2_1_6_1_634 2 141 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 186
  (Polychromatic418967fa.accept_11_1_9_10_1_184 1 141 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 141 186)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 140 186 (Eq.refl Bool.true)
  (allA_succ_of_gcd 46 140 186 2 23 70 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 140 186 (Polychromatic418967fa.accept_12_9_8_6_1_466 45 140 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 140 186 2 22 70 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 140 186 (accept_3_4 43 140 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 140 186 2 21 70 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 140 186 (Polychromatic418967fa.accept_15_11_5_6_1_669
  41 140 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 140 186 2 20 70 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 140 186
  (Polychromatic418967fa.accept_9_3_5_6_1_253 39 140 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 140 186 2 19 70 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 140 186 (accept_3_4 37 140 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 140 186 2 18 70 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 140 186 (Polychromatic418967fa.accept_9_8_5_6_1_538 35 140 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 140 186 2 17 70 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 140 186
  (Polychromatic418967fa.accept_12_9_8_6_1_466 33 140 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 140 186 2 16 70 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 140 186 (accept_3_4 31 140 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 140 186 2 15 70 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 140 186 (Polychromatic418967fa.accept_9_2_5_6_1_536 29 140 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 140 186 2 14 70 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 140 186
  (Polychromatic418967fa.accept_12_3_8_6_1_895 27 140 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 140 186 2 13 70 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 140 186 (accept_3_4 25 140 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 140 186 2 12 70 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 140 186 (Polychromatic418967fa.accept_29_23_24_12_1_4269 23 140 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 140 186 2 11 70 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 140 186
  (Polychromatic418967fa.accept_9_3_5_6_1_253 21 140 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 140 186 2 10 70 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 140 186 (accept_3_4 19 140 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 140 186 2 9 70 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 140 186 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 140 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 140 186 2 8 70 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 140 186 (Polychromatic418967fa.accept_12_3_8_6_1_895
  15 140 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 140 186 2 7 70 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 140 186
  (accept_3_4 13 140 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 140 186 2 6 70 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 140 186
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 140 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 140 186 2 5 70 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 140 186 (Polychromatic418967fa.accept_11_9_8_10_1_934 9 140 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 140 186 2 4 70 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 140 186 (accept_3_4 7 140 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 140 186 2 3 70 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 140 186 (Polychromatic418967fa.accept_13_5_10_4_1_1564 5 140 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 140 186 2 2 70 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 140 186 (Polychromatic418967fa.accept_9_3_5_6_1_253 3
  140 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 140 186 2 1 70 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 140 186 (accept_3_4 1
  140 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140 186)))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 48 139 186 (Eq.refl Bool.true) (allA_succ_of_accept 47 139 186 (accept_3_5 47 139 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 139 186 (Polychromatic418967fa.accept_9_1_4_6_1_5 46 139 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 139 186
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 139 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 139 186 (accept_3_5 44 139 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 139 186 (Polychromatic418967fa.accept_9_7_4_6_1_273 43 139 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 139 186 (Polychromatic418967fa.accept_19_4_6_15_1_7916 42 139 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 139 186 (accept_3_5 41 139 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 139 186 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 139 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 139 186
  (Polychromatic418967fa.accept_9_3_4_6_1_252 39 139 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 139 186 (accept_3_5 38 139 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 139 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 139 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 139 186 (Polychromatic418967fa.accept_11_3_7_10_1_180 36 139 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 139 186 (accept_3_5 35 139 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 139 186 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 139 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 139 186
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 139 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 139 186 (accept_3_5 32 139 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 139 186 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 139 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 139 186 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 139 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 139 186 (accept_3_5 29 139 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 139 186 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 139 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 139 186
  (Polychromatic418967fa.accept_18_9_13_6_1_877 27 139 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 139 186 (accept_3_5 26 139 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 139 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 139 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 139 186 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 139 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 139 186 (accept_3_5 23 139 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 139 186 (Polychromatic418967fa.accept_23_22_1_2_1_10699 22 139 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 139 186
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 139 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 139 186 (accept_3_5 20 139 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 139 186 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 139 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 139 186 (Polychromatic418967fa.accept_13_5_9_4_1_441 18 139 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 139 186 (accept_3_5 17 139 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 139 186 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 139 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 139 186
  (Polychromatic418967fa.accept_10_5_9_6_1_697 15 139 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 139 186 (accept_3_5 14 139 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 139 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 139 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 139 186 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 139 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 139 186 (accept_3_5 11 139 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 139 186 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 139 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 139 186
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 139 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 139 186 (accept_3_5 8 139 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  139 186 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 139 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 139 186 (Polychromatic418967fa.accept_13_6_9_4_1_2288 6 139 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 139 186 (accept_3_5 5 139 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 139 186 (Polychromatic418967fa.accept_17_4_3_16_1_9483 4 139 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 139 186
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 139 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 139 186 (accept_3_5 2 139 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  139 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 139 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 139 186)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 138 186 (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 138 186 6 8 23 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 138 186 (Polychromatic418967fa.accept_9_2_3_6_1_88 47 138 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 138 186 2 23 69 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 138 186 3 15 46 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 138 186 2 22 69 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 138 186
  (Polychromatic418967fa.accept_7_1_5_4_1_134 43 138 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 138 186 6 7 23 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 138 186 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 138 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 138 186 2 20 69 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 138 186 3 13 46 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 138 186 2 19 69 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 138 186
  (Polychromatic418967fa.accept_7_2_5_4_1_115 37 138 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 138 186 6 6 23 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 138 186 (Polychromatic418967fa.accept_9_8_3_6_1_533 35 138 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 138 186 2 17 69 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 138 186 3 11 46 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 138 186 2 16 69 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 138 186
  (Polychromatic418967fa.accept_9_4_3_6_1_532 31 138 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 138 186 6 5 23 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 138 186 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 138 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 138 186 2 14 69 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 138 186 3 9 46 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 138 186 2 13 69 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 138 186
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 138 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 138 186 6 4 23 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 138 186 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 138 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 138 186 2 11 69 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 138 186 3 7 46 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 138 186 2 10 69 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 138 186
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 138 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 138 186 6 3 23 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 138 186 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 138 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 138 186 2 8 69 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 138 186 3 5 46 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 138 186 2 7 69 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 138 186 (Polychromatic418967fa.accept_7_6_5_4_1_297 13
  138 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 138 186 6 2 23 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 138 186
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 138 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 138 186 2 5 69 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 138 186 3 3 46 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 138 186 2 4 69 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 138 186 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 138 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 138 186 6 1 23 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 138 186 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 138 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 138 186 2 2 69 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 138 186 3 1 46 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 138 186 2 1 69 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 138 186
  (Polychromatic418967fa.accept_7_1_5_4_1_134 1 138 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 138 186))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 137 186 (Eq.refl Bool.true)
  (allA_succ_of_accept 49 137 186 (accept_3_4 49 137 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 137 186 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 137 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 137 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 137 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 137 186 (accept_3_4 46 137 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 137 186 (Polychromatic418967fa.accept_13_6_7_4_1_2264 45 137 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 137 186
  (Polychromatic418967fa.accept_9_8_2_6_1_875 44 137 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 137 186 (accept_3_4 43 137 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 137 186 (Polychromatic418967fa.accept_13_3_7_4_1_435 42 137 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 137 186 (Polychromatic418967fa.accept_9_5_2_6_1_265 41 137 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 137 186 (accept_3_4 40 137 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 137 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 137 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 137 186
  (Polychromatic418967fa.accept_13_12_7_4_1_3124 38 137 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 137 186 (accept_3_4 37 137 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 137 186 (Polychromatic418967fa.accept_13_10_7_4_1_2262 36 137 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 137 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 137 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 137 186 (accept_3_4 34 137 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 137 186 (Polychromatic418967fa.accept_10_3_7_6_1_659 33 137 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 137 186
  (Polychromatic418967fa.accept_9_5_2_6_1_265 32 137 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 137 186 (accept_3_4 31 137 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 137 186 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 137 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 137 186 (Polychromatic418967fa.accept_13_3_7_4_1_435 29 137 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 137 186 (accept_3_4 28 137 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 137 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 137 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 137 186
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 137 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 137 186 (accept_3_4 25 137 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 137 186 (Polychromatic418967fa.accept_13_11_7_4_1_1561 24 137 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 137 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 137 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 137 186 (accept_3_4 22 137 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 137 186 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 137 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 137 186
  (Polychromatic418967fa.accept_19_1_4_15_1_2542 20 137 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 137 186 (accept_3_4 19 137 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 137 186 (Polychromatic418967fa.accept_19_18_4_15_1_3721 18 137 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 137 186 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 137 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 137 186 (accept_3_4 16 137 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 137 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 137 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 137 186
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 137 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 137 186 (accept_3_4 13 137 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 137 186 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 137 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 137 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 137 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 137 186 (accept_3_4 10 137 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 137 186 (Polychromatic418967fa.accept_13_9_7_4_1_953 9 137 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 186
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 137 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 137 186 (accept_3_4 7 137 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  137 186 (Polychromatic418967fa.accept_11_6_5_10_1_2724 6 137 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 137 186 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 137 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 186 (accept_3_4 4 137 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 137 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 137 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 137 186
  (Polychromatic418967fa.accept_17_2_1_16_1_6946 2 137 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 137 186 (accept_3_4 1 137 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 137
  186)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 136 186 (Eq.refl Bool.true) (allA_succ_of_gcd 50
  136 186 2 25 68 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 136 186 (Polychromatic418967fa.accept_9_4_1_6_1_284 49 136 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 136 186 2 24 68 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 136 186 (accept_3_5 47 136 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 136 186 2 23 68 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 136 186 (Polychromatic418967fa.accept_12_9_4_6_1_460 45 136 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 136 186 2 22 68 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 136 186
  (Polychromatic418967fa.accept_7_1_3_4_1_128 43 136 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 136 186 2 21 68 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 136 186 (accept_3_5 41 136 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 136 186 2 20 68 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 136 186 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 136 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 136 186 2 19 68 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 136 186
  (Polychromatic418967fa.accept_13_11_6_4_1_3121 37 136 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 136 186 2 18 68 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 136 186 (accept_3_5 35 136 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 136 186 2 17 68 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 136 186 (Polychromatic418967fa.accept_12_9_4_6_1_460 33 136 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 136 186 2 16 68 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 136 186
  (Polychromatic418967fa.accept_9_4_1_6_1_284 31 136 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 136 186 2 15 68 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 136 186 (accept_3_5 29 136 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 136 186 2 14 68 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 136 186 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 136 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 136 186 2 13 68 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 136 186
  (Polychromatic418967fa.accept_9_7_1_6_1_261 25 136 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 136 186 2 12 68 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 136 186 (accept_3_5 23 136 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 136 186 2 11 68 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 136 186 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 136 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 136 186 2 10 68 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 136 186
  (Polychromatic418967fa.accept_23_19_21_2_1_10698 19 136 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 136 186 2 9 68 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 136 186 (accept_3_5 17 136 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 136 186 2 8 68 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 136 186 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 136 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 136 186 2 7 68 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 136 186 (Polychromatic418967fa.accept_7_6_3_4_1_294 13
  136 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 136 186 2 6 68 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 136 186 (accept_3_5 11
  136 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 136 186 2 5 68 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 136 186
  (Polychromatic418967fa.accept_12_9_4_6_1_460 9 136 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 136 186 2 4 68 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 136 186 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 136 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 136 186 2 3 68 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 136 186 (accept_3_5 5 136 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 136 186 2 2 68 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 136 186 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 136 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 136 186 2 1 68 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 136 186 (Polychromatic418967fa.accept_7_1_3_4_1_128 1
  136 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 136
  186))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 135 186 (Eq.refl Bool.true) (allA_succ_of_gcd 51
  135 186 3 17 45 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 135 186 (Polychromatic418967fa.accept_12_2_3_6_1_112 50 135 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 135 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 135 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 135 186 3 16 45 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 135 186
  (Polychromatic418967fa.accept_7_5_2_4_1_126 47 135 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 135 186 (Polychromatic418967fa.accept_12_10_3_6_1_882 46 135 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 135 186 3 15 45 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 135 186 (Polychromatic418967fa.accept_10_4_5_6_1_651
  44 135 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 135 186
  (Polychromatic418967fa.accept_18_7_9_6_1_4023 43 135 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 135 186 3 14 45 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 135 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 135 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 135 186 (Polychromatic418967fa.accept_7_5_2_4_1_126
  40 135 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 135 186 3 13 45 62
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 135 186
  (Polychromatic418967fa.accept_12_2_3_6_1_112 38 135 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 135 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 135 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 135 186 3 12 45 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 135 186 (Polychromatic418967fa.accept_13_9_5_4_1_1591
  35 135 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 135 186
  (Polychromatic418967fa.accept_7_6_2_4_1_291 34 135 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 135 186 3 11 45 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 135 186 (Polychromatic418967fa.accept_12_8_3_6_1_909 32 135 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 135 186 (Polychromatic418967fa.accept_10_1_5_6_1_649
  31 135 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 135 186 3 10 45 62
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 135 186
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 135 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 135 186 (Polychromatic418967fa.accept_12_4_3_6_1_879 28 135 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 135 186 3 9 45 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 135 186 (Polychromatic418967fa.accept_7_5_2_4_1_126 26
  135 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 135 186
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 135 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 135 186 3 8 45 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 135 186 (Polychromatic418967fa.accept_13_10_5_4_1_3107 23 135 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 135 186 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 135
  186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 135 186 3 7 45 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 135 186
  (Polychromatic418967fa.accept_7_6_2_4_1_291 20 135 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 135 186 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 135 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 135 186 3 6 45 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 135 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 17
  135 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 135 186
  (Polychromatic418967fa.accept_12_4_3_6_1_879 16 135 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 135 186 3 5 45 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 135 186 (Polychromatic418967fa.accept_10_4_5_6_1_651 14 135 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 135 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 135 186 3 4 45 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 135 186
  (Polychromatic418967fa.accept_10_1_5_6_1_649 11 135 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 135 186 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 135 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 135 186 3 3 45 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 135 186 (Polychromatic418967fa.accept_12_8_3_6_1_909 8 135 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 186
  (Polychromatic418967fa.accept_11_7_3_10_1_1461 7 135 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 135 186 3 2 45 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 135 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 135 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 135 186 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 135 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 135 186 3 1 45 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 135 186
  (Polychromatic418967fa.accept_12_2_3_6_1_112 2 135 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 135 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 135 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 135 186)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53
  134 186 (Eq.refl Bool.true) (allA_succ_of_gcd 52 134 186 2 26 67 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 134 186 (Polychromatic418967fa.accept_12_3_2_6_1_138 51 134 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 134 186 2 25 67 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 134 186 (accept_3_4 49
  134 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 134 186 2 24 67 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 134 186
  (Polychromatic418967fa.accept_7_5_1_4_1_122 47 134 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 134 186 2 23 67 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 134 186 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 134 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 134 186 2 22 67 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 134 186 (accept_3_4 43 134 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 134 186 2 21 67 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 134 186 (Polychromatic418967fa.accept_9_5_8_6_1_281 41
  134 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 134 186 2 20 67 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 134 186
  (Polychromatic418967fa.accept_9_3_8_6_1_80 39 134 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 134 186 2 19 67 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 134 186 (accept_3_4 37 134 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 134 186 2 18 67 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 134 186 (Polychromatic418967fa.accept_10_5_4_6_1_319 35 134 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 134 186 2 17 67 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 134 186
  (Polychromatic418967fa.accept_7_5_1_4_1_122 33 134 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 134 186 2 16 67 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 134 186 (accept_3_4 31 134 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 134 186 2 15 67 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 134 186 (Polychromatic418967fa.accept_9_2_8_6_1_79 29 134 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 134 186 2 14 67 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 134 186
  (Polychromatic418967fa.accept_12_3_2_6_1_138 27 134 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 134 186 2 13 67 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 134 186 (accept_3_4 25 134 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 134 186 2 12 67 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 134 186 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 134 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 134 186 2 11 67 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 134 186
  (Polychromatic418967fa.accept_9_3_8_6_1_80 21 134 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 134 186 2 10 67 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 134 186 (accept_3_4 19 134 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 134 186 2 9 67 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 134 186 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 134 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 134 186 2 8 67 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 134 186 (Polychromatic418967fa.accept_10_5_4_6_1_319
  15 134 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 134 186 2 7 67 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 134 186
  (accept_3_4 13 134 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 134 186 2 6 67 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 134 186
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 134 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 134 186 2 5 67 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 134 186 (Polychromatic418967fa.accept_12_9_2_6_1_455 9 134 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 134 186 2 4 67 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 134 186 (accept_3_4 7 134 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 134 186 2 3 67 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 134 186 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 134 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 134 186 2 2 67 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 134 186 (Polychromatic418967fa.accept_7_3_1_4_1_121 3
  134 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 134 186 2 1 67 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 134 186 (accept_3_4 1
  134 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134
  186))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 133 186 (Eq.refl Bool.true)
  (allA_succ_of_accept 53 133 186 (accept_3_5 53 133 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 133 186 (Polychromatic418967fa.accept_14_10_7_4_1_3453 52 133 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 133 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 133 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 133 186 (accept_3_5 50 133 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 133 186 (Polychromatic418967fa.accept_9_4_7_6_1_255 49 133 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 133 186
  (Polychromatic418967fa.accept_9_3_7_6_1_76 48 133 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 133 186 (accept_3_5 47 133 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 133 186 (Polychromatic418967fa.accept_9_1_7_6_1_75 46 133 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 133 186 (Polychromatic418967fa.accept_14_3_7_4_1_118 45 133 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 133 186 (accept_3_5 44 133 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 133 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 133 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 133 186
  (Polychromatic418967fa.accept_11_9_1_10_1_920 42 133 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 133 186 (accept_3_5 41 133 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 133 186 (Polychromatic418967fa.accept_9_4_7_6_1_255 40 133 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 133 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 133 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 133 186 (accept_3_5 38 133 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 133 186 (Polychromatic418967fa.accept_9_1_7_6_1_75 37 133 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 133 186
  (Polychromatic418967fa.accept_17_2_14_16_1_2187 36 133 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 133 186 (accept_3_5 35 133 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 133 186 (Polychromatic418967fa.accept_15_4_13_6_1_642 34 133 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 133 186 (Polychromatic418967fa.accept_13_7_3_4_1_459 33 133
  186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 133 186 (accept_3_5 32 133
  186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 133 186
  (Polychromatic418967fa.accept_4_3_1_2_1_62 31 133 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 133 186 (Polychromatic418967fa.accept_9_3_7_6_1_76 30 133 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 133 186 (accept_3_5 29 133 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 133 186 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 133 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 133 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 27
  133 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 133 186 (accept_3_5 26
  133 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 133 186
  (Polychromatic418967fa.accept_13_12_3_4_1_928 25 133 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 133 186 (Polychromatic418967fa.accept_11_2_1_10_1_196 24 133 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 133 186 (accept_3_5 23 133 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 133 186 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 133 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 133 186 (Polychromatic418967fa.accept_9_3_7_6_1_76 21
  133 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 133 186 (accept_3_5 20
  133 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 133 186
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 133 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 133 186 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 133 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 133 186 (accept_3_5 17 133 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 133 186 (Polychromatic418967fa.accept_23_16_18_2_1_10697 16 133 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 133 186
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 133 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 133 186 (accept_3_5 14 133 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 133 186 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 133 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 133 186 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 133 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 133 186 (accept_3_5 11 133 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 133 186 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 133 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 133 186
  (Polychromatic418967fa.accept_10_9_3_6_1_686 9 133 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 133 186 (accept_3_5 8 133 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  133 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 133 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 133 186 (Polychromatic418967fa.accept_21_6_7_18_1_1783 6 133 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 133 186 (accept_3_5 5 133 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 133 186 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 133 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 133 186
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 133 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 133 186 (accept_3_5 2 133 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  133 186 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 133 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 133 186)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 132 186 (Eq.refl
  Bool.true) (allA_succ_of_gcd 54 132 186 6 9 22 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 132 186 (Polychromatic418967fa.accept_21_11_6_18_1_4450 53 132 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 132 186 2 26 66 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 132 186 3 17 44 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 132 186 2 25 66 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 132 186
  (Polychromatic418967fa.accept_21_7_6_18_1_7681 49 132 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 132 186 6 8 22 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 132 186 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 132 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 132 186 2 23 66 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 132 186 3 15 44 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 132 186 2 22 66 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 132 186
  (Polychromatic418967fa.accept_17_9_13_16_1_3266 43 132 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 132 186 6 7 22 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 132 186 (Polychromatic418967fa.accept_10_1_2_6_1_638 41 132 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 132 186 2 20 66 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 132 186 3 13 44 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 132 186 2 19 66 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 132 186
  (Polychromatic418967fa.accept_7_2_6_4_1_29 37 132 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 132 186 6 6 22 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 132 186 (Polychromatic418967fa.accept_15_5_12_6_1_639 35 132 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 132 186 2 17 66 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 132 186 3 11 44 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 132 186 2 16 66 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 132 186
  (Polychromatic418967fa.accept_7_3_6_4_1_30 31 132 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 132 186 6 5 22 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 132 186 (Polychromatic418967fa.accept_17_12_13_16_1_3226 29 132 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 132 186 2 14 66 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 132 186 3 9 44 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 132 186 2 13 66 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 132 186
  (Polychromatic418967fa.accept_13_12_2_4_1_3131 25 132 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 132 186 6 4 22 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 132 186 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 132 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 132 186 2 11 66 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 132 186 3 7 44 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 132 186 2 10 66 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 132 186
  (Polychromatic418967fa.accept_7_5_6_4_1_117 19 132 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 132 186 6 3 22 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 132 186 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 132 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 132 186 2 8 66 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 132 186 3 5 44 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 132 186 2 7 66 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 132 186
  (Polychromatic418967fa.accept_21_13_6_18_1_10696 13 132 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 132 186 6 2 22 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 132 186 (Polychromatic418967fa.accept_10_1_2_6_1_638 11 132 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 132 186 2 5 66 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 132 186 3 3 44 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 132 186 2 4 66 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 132 186
  (Polychromatic418967fa.accept_15_7_12_6_1_1327 7 132 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 132 186 6 1 22 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 132 186 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 132 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 132 186 2 2 66 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 132 186 3 1 44 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 132 186 2 1 66 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 132 186 (Polychromatic418967fa.accept_10_1_2_6_1_638 1 132 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132
  186))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 131 186 (Eq.refl Bool.true)
  (allA_succ_of_accept 55 131 186 (accept_3_4 55 131 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 131 186 (Polychromatic418967fa.accept_15_9_11_6_1_637 54 131 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 131 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 131 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 131 186 (accept_3_4 52 131 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 131 186 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 131 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 131 186
  (Polychromatic418967fa.accept_7_1_5_4_1_134 50 131 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 131 186 (accept_3_4 49 131 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 131 186 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 131 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 131 186 (Polychromatic418967fa.accept_9_2_5_6_1_536 47 131 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 131 186 (accept_3_4 46 131 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 131 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 131 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 131 186
  (Polychromatic418967fa.accept_7_2_5_4_1_115 44 131 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 131 186 (accept_3_4 43 131 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 131 186 (Polychromatic418967fa.accept_10_2_1_6_1_634 42 131 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 131 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 131 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 131 186 (accept_3_4 40 131 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 131 186 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 131 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 131 186
  (Polychromatic418967fa.accept_9_2_5_6_1_536 38 131 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 131 186 (accept_3_4 37 131 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 131 186 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 131 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 131 186 (Polychromatic418967fa.accept_9_8_5_6_1_538 35 131 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 131 186 (accept_3_4 34 131 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 131 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 131 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 131 186
  (Polychromatic418967fa.accept_10_2_1_6_1_634 32 131 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 131 186 (accept_3_4 31 131 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 131 186 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 131 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 131 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 131 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 131 186 (accept_3_4 28 131 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 131 186 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 131 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 131 186
  (Polychromatic418967fa.accept_9_8_5_6_1_538 26 131 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 131 186 (accept_3_4 25 131 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 131 186 (Polychromatic418967fa.accept_15_9_11_6_1_637 24 131 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 131 186 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 131 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 131 186 (accept_3_4 22 131 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 131 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 131 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 131 186
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 131 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 131 186 (accept_3_4 19 131 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 131 186 (Polychromatic418967fa.accept_13_5_1_4_1_3966 18 131 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 131 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 131 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 131 186 (accept_3_4 16 131 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 131 186 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 131 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 131 186
  (Polychromatic418967fa.accept_19_14_17_15_1_3761 14 131 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 131 186 (accept_3_4 13 131 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 131 186 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 131 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 131 186 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 131 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 131 186 (accept_3_4 10 131 186
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 131 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 9
  131 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 131 186
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 131 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 131 186 (accept_3_4 7 131 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  131 186 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 131 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 131 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 131 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 131 186 (accept_3_4 4 131 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 131 186 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 131 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 131 186
  (Polychromatic418967fa.accept_7_2_5_4_1_115 2 131 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 131 186 (accept_3_4 1 131 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 131
  186)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 130 186 (Eq.refl Bool.true)
  (allA_succ_of_gcd 56 130 186 2 28 65 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 130 186 (Polychromatic418967fa.accept_9_1_4_6_1_5 55 130 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 130 186 2 27 65 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 130 186 (accept_3_5 53 130 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 130 186 2 26 65 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 130 186 (Polychromatic418967fa.accept_12_3_10_6_1_442
  51 130 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 130 186 2 25 65 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 130 186
  (Polychromatic418967fa.accept_15_4_10_6_1_2997 49 130 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 130 186 2 24 65 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 130 186 (accept_3_5 47 130 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 130 186 2 23 65 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 130 186 (Polychromatic418967fa.accept_11_1_9_10_1_184 45 130 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 130 186 2 22 65 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 130 186
  (Polychromatic418967fa.accept_9_7_4_6_1_273 43 130 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 130 186 2 21 65 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 130 186 (accept_3_5 41 130 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 130 186 2 20 65 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 130 186 (Polychromatic418967fa.accept_9_3_4_6_1_252 39 130 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 130 186 2 19 65 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 130 186
  (Polychromatic418967fa.accept_9_1_4_6_1_5 37 130 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 130 186 2 18 65 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 130 186 (accept_3_5 35 130 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 130 186 2 17 65 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 130 186 (Polychromatic418967fa.accept_12_9_10_6_1_872 33 130 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 130 186 2 16 65 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 130 186
  (Polychromatic418967fa.accept_15_1_10_6_1_631 31 130 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 130 186 2 15 65 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 130 186 (accept_3_5 29 130 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 130 186 2 14 65 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 130 186 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 130 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 130 186 2 13 65 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 130 186
  (Polychromatic418967fa.accept_9_7_4_6_1_273 25 130 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 130 186 2 12 65 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 130 186 (accept_3_5 23 130 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 130 186 2 11 65 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 130 186 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 130 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 130 186 2 10 65 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 130 186
  (Polychromatic418967fa.accept_9_1_4_6_1_5 19 130 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 130 186 2 9 65 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 130 186 (accept_3_5 17 130 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  130 186 2 8 65 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 130 186 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 130 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 130 186 2 7 65 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 130 186 (Polychromatic418967fa.accept_19_13_16_15_1_3781 13 130 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 130 186 2 6 65 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 130 186 (accept_3_5 11
  130 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 130 186 2 5 65 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 130 186
  (Polychromatic418967fa.accept_12_9_10_6_1_872 9 130 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 130 186 2 4 65 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 130 186 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 130 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 130 186 2 3 65 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 130 186 (accept_3_5 5 130 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 130 186 2 2 65 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 130 186 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 130 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 130 186 2 1 65 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 130 186 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 130
  186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 130
  186))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 129 186 (Eq.refl Bool.true)
  (allA_succ_of_gcd 57 129 186 3 19 43 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 129 186 (Polychromatic418967fa.accept_9_2_3_6_1_88 56 129 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 129 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 55
  129 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 129 186 3 18 43 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 129 186
  (Polychromatic418967fa.accept_9_8_3_6_1_533 53 129 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 129 186 (Polychromatic418967fa.accept_9_7_3_6_1_270 52 129 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 129 186 3 17 43 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 129 186 (Polychromatic418967fa.accept_7_1_3_4_1_128 50
  129 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 129 186
  (Polychromatic418967fa.accept_9_4_3_6_1_532 49 129 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 129 186 3 16 43 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 129 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 129 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 129 186 (Polychromatic418967fa.accept_9_1_3_6_1_70 46
  129 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 129 186 3 15 43 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 129 186
  (Polychromatic418967fa.accept_9_8_3_6_1_533 44 129 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 129 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 129 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 129 186 3 14 43 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 129 186 (Polychromatic418967fa.accept_7_6_3_4_1_294 41
  129 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 129 186
  (Polychromatic418967fa.accept_9_4_3_6_1_532 40 129 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 129 186 3 13 43 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 129 186 (Polychromatic418967fa.accept_9_2_3_6_1_88 38 129 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 129 186 (Polychromatic418967fa.accept_9_1_3_6_1_70 37
  129 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 129 186 3 12 43 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 129 186
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 129 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 129 186 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 129 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 129 186 3 11 43 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 129 186 (Polychromatic418967fa.accept_9_5_3_6_1_269 32
  129 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 129 186
  (Polychromatic418967fa.accept_4_3_1_2_1_62 31 129 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 129 186 3 10 43 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 129 186 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 129 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 129 186 (Polychromatic418967fa.accept_9_1_3_6_1_70 28
  129 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 129 186 3 9 43 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 129 186
  (Polychromatic418967fa.accept_9_8_3_6_1_533 26 129 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 129 186 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 129 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 129 186 3 8 43 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 129 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 23
  129 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 186
  (Polychromatic418967fa.accept_7_1_3_4_1_128 22 129 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 129 186 3 7 43 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 129 186 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 129 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 129 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 129 186 3 6 43 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 129 186
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 129 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 129 186 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 129 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 129 186 3 5 43 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 129 186 (Polychromatic418967fa.accept_9_5_3_6_1_269 14
  129 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 186
  (Polychromatic418967fa.accept_7_6_3_4_1_294 13 129 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 129 186 3 4 43 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 129 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 129 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 186 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 129 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 129 186 3 3 43 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 129 186
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 129 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 129 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 129 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 129 186 3 2 43 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 129 186 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 129 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 186
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 129 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 129 186 3 1 43 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 129 186 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 129 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 186 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 129 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129
  186)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 128 186 (Eq.refl Bool.true)
  (allA_succ_of_gcd 58 128 186 2 29 64 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 128 186 (Polychromatic418967fa.accept_9_3_2_6_1_264 57 128 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 128 186 2 28 64 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 128 186 (accept_3_4 55 128 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 128 186 2 27 64 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 128 186 (Polychromatic418967fa.accept_9_8_2_6_1_875 53
  128 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 128 186 2 26 64 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 128 186
  (Polychromatic418967fa.accept_12_3_8_6_1_895 51 128 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 128 186 2 25 64 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 128 186 (accept_3_4 49 128 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 128 186 2 24 64 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 128 186 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 128 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 128 186 2 23 64 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 128 186
  (Polychromatic418967fa.accept_12_9_8_6_1_466 45 128 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 128 186 2 22 64 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 128 186 (accept_3_4 43 128 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 128 186 2 21 64 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 128 186 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 128 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 128 186 2 20 64 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 128 186
  (Polychromatic418967fa.accept_9_3_2_6_1_264 39 128 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 128 186 2 19 64 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 128 186 (accept_3_4 37 128 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 128 186 2 18 64 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 128 186 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 128 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 128 186 2 17 64 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 128 186
  (Polychromatic418967fa.accept_7_5_2_4_1_126 33 128 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 128 186 2 16 64 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 128 186 (accept_3_4 31 128 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 128 186 2 15 64 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 128 186 (Polychromatic418967fa.accept_15_14_8_6_1_2133 29 128 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 128 186 2 14 64 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 128 186
  (Polychromatic418967fa.accept_7_6_2_4_1_291 27 128 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 128 186 2 13 64 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 128 186 (accept_3_4 25 128 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 128 186 2 12 64 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 128 186 (Polychromatic418967fa.accept_9_5_2_6_1_265 23 128 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 128 186 2 11 64 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 128 186
  (Polychromatic418967fa.accept_9_3_2_6_1_264 21 128 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 128 186 2 10 64 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 128 186 (accept_3_4 19 128 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 128 186 2 9 64 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 128 186 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 128 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 128 186 2 8 64 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 128 186 (Polychromatic418967fa.accept_12_3_8_6_1_895
  15 128 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 128 186 2 7 64 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 128 186
  (accept_3_4 13 128 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 128 186 2 6 64 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 128 186
  (Polychromatic418967fa.accept_19_11_14_15_1_9276 11 128 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 128 186 2 5 64 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 128 186 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 128 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 128 186 2 4 64 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 128 186 (accept_3_4 7 128 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 128 186 2 3 64 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 128 186 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 128 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 128 186 2 2 64 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 128 186
  (Polychromatic418967fa.accept_9_3_2_6_1_264 3 128 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 128 186 2 1 64 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 128 186 (accept_3_4 1 128 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128
  186))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 127 186 (Eq.refl Bool.true)
  (allA_succ_of_accept 59 127 186 (accept_3_5 59 127 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 127 186 (Polychromatic418967fa.accept_9_4_1_6_1_284 58 127 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 127 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 127 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 127 186 (accept_3_5 56 127 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 127 186 (Polychromatic418967fa.accept_19_17_13_15_1_1402 55 127 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 127 186
  (Polychromatic418967fa.accept_7_5_1_4_1_122 54 127 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 127 186 (accept_3_5 53 127 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 127 186 (Polychromatic418967fa.accept_7_3_1_4_1_121 52 127 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 127 186 (Polychromatic418967fa.accept_10_1_7_6_1_91 51 127 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 127 186 (accept_3_5 50 127 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 127 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 127 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 127 186
  (Polychromatic418967fa.accept_9_3_1_6_1_86 48 127 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 127 186 (accept_3_5 47 127 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 127 186 (Polychromatic418967fa.accept_13_7_10_4_1_919 46 127 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 127 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 127 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 127 186 (accept_3_5 44 127 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 127 186 (Polychromatic418967fa.accept_9_7_1_6_1_261 43 127 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 127 186
  (Polychromatic418967fa.accept_15_12_7_6_1_4013 42 127 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 127 186 (accept_3_5 41 127 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 127 186 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 127 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 127 186 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 127 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 127 186 (accept_3_5 38 127 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 127 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 127 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 127 186
  (Polychromatic418967fa.accept_17_2_8_16_1_4403 36 127 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 127 186 (accept_3_5 35 127 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 127 186 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 127 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 127 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 127 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 127 186 (accept_3_5 32 127 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 127 186 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 127 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 127 186
  (Polychromatic418967fa.accept_9_3_1_6_1_86 30 127 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 127 186 (accept_3_5 29 127 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 127 186 (Polychromatic418967fa.accept_15_13_7_6_1_682 28 127 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 127 186 (Polychromatic418967fa.accept_11_5_6_10_1_1432 27 127 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 127 186 (accept_3_5 26 127 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 127 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 127 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 127 186
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 127 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 127 186 (accept_3_5 23 127 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 127 186 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 127 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 127 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 127 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 127 186 (accept_3_5 20 127 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 127 186 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 127 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 127 186
  (Polychromatic418967fa.accept_13_5_10_4_1_1564 18 127 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 127 186 (accept_3_5 17 127 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 127 186 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 127 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 127 186 (Polychromatic418967fa.accept_21_15_1_18_1_3066 15 127 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 127 186 (accept_3_5 14 127 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 127 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 127 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 127 186
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 127 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 127 186 (accept_3_5 11 127 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 127 186 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 127 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 127 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 127 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 127 186 (accept_3_5 8 127 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 127 186 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 127 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 127 186
  (Polychromatic418967fa.accept_13_6_10_4_1_957 6 127 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 127 186 (accept_3_5 5 127 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  127 186 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 127 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 127 186 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 127 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 127 186 (accept_3_5 2 127 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 127 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 127 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 127
  186)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 126 186 (Eq.refl Bool.true)
  (allA_succ_of_gcd 60 126 186 6 10 21 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 126 186 (Polychromatic418967fa.accept_11_4_5_10_1_926 59 126 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 126 186 2 29 63 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 126 186 3 19 42 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 126 186 2 28 63 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 126 186
  (Polychromatic418967fa.accept_16_7_14_10_1_3544 55 126 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 126 186 6 9 21 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 126 186 (Polychromatic418967fa.accept_16_5_14_10_1_3644 53 126 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 126 186 2 26 63 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 126 186 3 17 42 62
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 126 186 2 25 63
  93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 126 186
  (Polychromatic418967fa.accept_22_5_16_10_1_7349 49 126 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 126 186 6 8 21 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 126 186 (Polychromatic418967fa.accept_13_8_9_4_1_1552 47 126 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 126 186 2 23 63 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 126 186 3 15 42 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 126 186 2 22 63 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 126 186
  (Polychromatic418967fa.accept_19_5_12_15_1_9244 43 126 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 126 186 6 7 21 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 126 186 (Polychromatic418967fa.accept_19_3_12_15_1_568 41 126 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 126 186 2 20 63 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 126 186 3 13 42 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 126 186 2 19 63 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 126 186
  (Polychromatic418967fa.accept_11_4_5_10_1_926 37 126 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 126 186 6 6 21 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 126 186 (Polychromatic418967fa.accept_19_16_12_15_1_6449 35 126 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 126 186 2 17 63 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 126 186 3 11 42 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 126 186 2 16 63 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 126 186
  (Polychromatic418967fa.accept_13_5_9_4_1_441 31 126 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 126 186 6 5 21 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 126 186 (Polychromatic418967fa.accept_16_13_14_10_1_1669 29 126 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 126 186 2 14 63 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 126 186 3 9 42 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 126 186 2 13 63 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 126 186
  (Polychromatic418967fa.accept_17_8_7_16_1_9508 25 126 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 126 186 6 4 21 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 126 186 (Polychromatic418967fa.accept_16_7_14_10_1_3544 23 126 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 126 186 2 11 63 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 126 186 3 7 42 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 126 186 2 10 63 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 126 186
  (Polychromatic418967fa.accept_13_6_9_4_1_2288 19 126 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 126 186 6 3 21 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 126 186 (Polychromatic418967fa.accept_11_6_5_10_1_2724 17 126 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 126 186 2 8 63 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 126 186 3 5 42 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 126 186 2 7 63 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 126 186
  (Polychromatic418967fa.accept_16_13_14_10_1_1669 13 126 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 126 186 6 2 21 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 126 186 (Polychromatic418967fa.accept_24_11_6_18_1_10695 11 126 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 126 186 2 5 63 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 126 186 3 3 42 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 126 186 2 4 63 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 126 186
  (Polychromatic418967fa.accept_13_7_9_4_1_918 7 126 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 126 186 6 1 21 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 126 186 (Polychromatic418967fa.accept_13_5_9_4_1_441 5 126 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 126 186 2 2 63 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 126 186 3 1 42 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 126 186 2 1 63 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 126 186 (Polychromatic418967fa.accept_24_1_6_18_1_10694 1 126
  186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  186))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 125 186 (Eq.refl Bool.true)
  (allA_succ_of_accept 61 125 186 (accept_3_4 61 125 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 125 186 (Polychromatic418967fa.accept_11_5_4_10_1_524 60 125 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 125 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 125 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 125 186 (accept_3_4 58 125 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 125 186 (Polychromatic418967fa.accept_9_3_8_6_1_80 57 125 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 125 186
  (Polychromatic418967fa.accept_9_2_8_6_1_79 56 125 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 125 186 (accept_3_4 55 125 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 125 186 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 125 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 125 186 (Polychromatic418967fa.accept_16_5_13_10_1_3664 53 125 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 125 186 (accept_3_4 52 125 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 125 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 125 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 125 186
  (Polychromatic418967fa.accept_9_5_8_6_1_281 50 125 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 125 186 (accept_3_4 49 125 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 125 186 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 125 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 125 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 125 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 125 186 (accept_3_4 46 125 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 125 186 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 125 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 125 186
  (Polychromatic418967fa.accept_7_2_6_4_1_29 44 125 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 125 186 (accept_3_4 43 125 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 125 186 (Polychromatic418967fa.accept_15_12_5_6_1_2148 42 125 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 125 186 (Polychromatic418967fa.accept_9_5_8_6_1_281 41 125 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 125 186 (accept_3_4 40 125 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 125 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 125 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 125 186
  (Polychromatic418967fa.accept_7_3_6_4_1_30 38 125 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 125 186 (accept_3_4 37 125 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 125 186 (Polychromatic418967fa.accept_13_10_8_4_1_3098 36 125 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 125 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 125 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 125 186 (accept_3_4 34 125 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 125 186 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 125 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 125 186
  (Polychromatic418967fa.accept_9_5_8_6_1_281 32 125 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 125 186 (accept_3_4 31 125 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 125 186 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 125 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 125 186 (Polychromatic418967fa.accept_9_2_8_6_1_79 29 125 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 125 186 (accept_3_4 28 125 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 125 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 125 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 125 186
  (Polychromatic418967fa.accept_7_5_6_4_1_117 26 125 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 125 186 (accept_3_4 25 125 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 125 186 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 125 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 125 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 125 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 125 186 (accept_3_4 22 125 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 125 186 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 125 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 125 186
  (Polychromatic418967fa.accept_9_2_8_6_1_79 20 125 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 125 186 (accept_3_4 19 125 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 125 186 (Polychromatic418967fa.accept_15_3_5_6_1_4005 18 125 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 125 186 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 125 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 125 186 (accept_3_4 16 125 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 125 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 125 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 125 186
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 125 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 125 186 (accept_3_4 13 125 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 125 186 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 125 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 125 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 125 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 125 186 (accept_3_4 10 125 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 125 186 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 125 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 125 186
  (Polychromatic418967fa.accept_23_8_10_2_1_10693 8 125 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 125 186 (accept_3_4 7 125 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  125 186 (Polychromatic418967fa.accept_19_6_11_15_1_2527 6 125 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 125 186 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 125 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 125 186 (accept_3_4 4 125 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 125 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 125 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 125 186
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 125 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 125 186 (accept_3_4 1 125 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 125
  186)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 124 186 (Eq.refl Bool.true)
  (allA_succ_of_gcd 62 124 186 62 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 124 186 (Polychromatic418967fa.accept_13_9_7_4_1_953 61 124 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 124 186 2 30 62 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 124 186 (accept_3_5 59 124 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 58 124 186 2 29 62 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 124 186 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 124 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 124 186 2 28 62 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 124 186
  (Polychromatic418967fa.accept_7_6_5_4_1_297 55 124 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 124 186 2 27 62 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 124 186 (accept_3_5 53 124 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 124 186 2 26 62 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 124 186 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 124 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 124 186 2 25 62 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 124 186
  (Polychromatic418967fa.accept_9_4_7_6_1_255 49 124 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 124 186 2 24 62 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 124 186 (accept_3_5 47 124 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 124 186 2 23 62 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 124 186 (Polychromatic418967fa.accept_10_5_4_6_1_319 45 124 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 124 186 2 22 62 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 124 186
  (Polychromatic418967fa.accept_7_1_5_4_1_134 43 124 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 124 186 2 21 62 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 124 186 (accept_3_5 41 124 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 124 186 2 20 62 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 124 186 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 124 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 124 186 2 19 62 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 124 186
  (Polychromatic418967fa.accept_7_2_5_4_1_115 37 124 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 124 186 2 18 62 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 124 186 (accept_3_5 35 124 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 124 186 2 17 62 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 124 186 (Polychromatic418967fa.accept_12_9_4_6_1_460 33 124 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 124 186 2 16 62 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 31 124 186 31 1 4 6 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 30 124 186 2 15 62 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 124 186 (accept_3_5 29 124 186
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 124 186 2 14 62 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 124 186
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 124 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 124 186 2 13 62 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 124 186 (Polychromatic418967fa.accept_10_5_4_6_1_319 25 124 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 124 186 2 12 62 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 124 186 (accept_3_5 23 124 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 124 186 2 11 62 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 124 186 (Polychromatic418967fa.accept_9_3_7_6_1_76 21
  124 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 124 186 2 10 62 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 124 186
  (Polychromatic418967fa.accept_9_1_7_6_1_75 19 124 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 124 186 2 9 62 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 124 186 (accept_3_5 17 124 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  124 186 2 8 62 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 124 186 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 124 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 124 186 2 7 62 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 124 186 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 124 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 124 186 2 6 62 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 124 186 (accept_3_5 11 124 186
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 124 186 2 5 62 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 124 186
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 124 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 124 186 2 4 62 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 124 186 (Polychromatic418967fa.accept_11_7_3_10_1_1461 7 124 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 124 186 2 3 62 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 124 186 (accept_3_5 5 124 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 124 186 2 2 62 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 124 186 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 124 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 124 186 2 1 62 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 124 186 (Polychromatic418967fa.accept_7_1_5_4_1_134 1
  124 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 124
  186))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 123 186 (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 123 186 3 21 41 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 123 186 (Polychromatic418967fa.accept_12_2_3_6_1_112 62 123 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 123 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 61
  123 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 123 186 3 20 41 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 123 186
  (Polychromatic418967fa.accept_10_9_3_6_1_686 59 123 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 123 186 (Polychromatic418967fa.accept_10_8_3_6_1_685 58 123 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 123 186 3 19 41 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 123 186 (Polychromatic418967fa.accept_11_1_2_10_1_1426
  56 123 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 123 186
  (Polychromatic418967fa.accept_15_10_3_6_1_3042 55 123 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 123 186 3 18 41 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 123 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 123 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 123 186 (Polychromatic418967fa.accept_12_4_3_6_1_879
  52 123 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 123 186 3 17 41 62
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 123 186
  (Polychromatic418967fa.accept_12_2_3_6_1_112 50 123 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 123 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 123 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 123 186 3 16 41 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 123 186 (Polychromatic418967fa.accept_10_7_3_6_1_644
  47 123 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 123 186
  (Polychromatic418967fa.accept_12_10_3_6_1_882 46 123 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 123 186 3 15 41 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 123 186 (Polychromatic418967fa.accept_12_8_3_6_1_909 44 123 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 123 186
  (Polychromatic418967fa.accept_14_1_11_4_1_3430 43 123 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 123 186 3 14 41 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 123 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 123 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 123 186 (Polychromatic418967fa.accept_12_4_3_6_1_879
  40 123 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 123 186 3 13 41 62
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 123 186
  (Polychromatic418967fa.accept_10_8_3_6_1_685 38 123 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 123 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 123 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 123 186 3 12 41 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 123 186 (Polychromatic418967fa.accept_13_9_6_4_1_2243
  35 123 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 123 186
  (Polychromatic418967fa.accept_11_1_2_10_1_1426 34 123 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 123 186 3 11 41 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 123 186 (Polychromatic418967fa.accept_12_8_3_6_1_909 32 123 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 186 (Polychromatic418967fa.accept_13_5_6_4_1_1582
  31 123 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 123 186 3 10 41 62
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 123 186
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 123 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 123 186 (Polychromatic418967fa.accept_10_8_3_6_1_685 28 123 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 123 186 3 9 41 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 123 186 (Polychromatic418967fa.accept_12_2_3_6_1_112
  26 123 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 186
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 123 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 123 186 3 8 41 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 123 186 (Polychromatic418967fa.accept_11_1_2_10_1_1426 23 123 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 123 186 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 123
  186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 123 186 3 7 41 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 123 186
  (Polychromatic418967fa.accept_12_8_3_6_1_909 20 123 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 123 186 (Polychromatic418967fa.accept_10_9_3_6_1_686 19 123 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 123 186 3 6 41 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 123 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 17
  123 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 123 186
  (Polychromatic418967fa.accept_12_4_3_6_1_879 16 123 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 123 186 3 5 41 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 123 186 (Polychromatic418967fa.accept_12_2_3_6_1_112 14 123 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 123 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 123 186 3 4 41 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 123 186
  (Polychromatic418967fa.accept_13_11_6_4_1_3121 11 123 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 123 186 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 123 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 123 186 3 3 41 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 123 186 (Polychromatic418967fa.accept_10_8_3_6_1_685 8 123 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 186
  (Polychromatic418967fa.accept_10_7_3_6_1_644 7 123 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 123 186 3 2 41 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 123 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 123 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 186 (Polychromatic418967fa.accept_12_4_3_6_1_879 4 123 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 123 186 3 1 41 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 123 186
  (Polychromatic418967fa.accept_12_2_3_6_1_112 2 123 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 123 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 123 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 123 186))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 65 122 186 (Eq.refl Bool.true) (allA_succ_of_gcd 64 122 186 2 32 61 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 122 186
  (Polychromatic418967fa.accept_12_3_2_6_1_138 63 122 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 122 186 2 31 61 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 122 186 (accept_3_4 61 122 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 122 186 2 30 61 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 122 186 (Polychromatic418967fa.accept_19_2_8_15_1_2447 59 122 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 122 186 2 29 61 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 122 186
  (Polychromatic418967fa.accept_7_1_3_4_1_128 57 122 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 122 186 2 28 61 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 122 186 (accept_3_4 55 122 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 122 186 2 27 61 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 122 186 (Polychromatic418967fa.accept_9_8_5_6_1_538 53 122 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 122 186 2 26 61 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 122 186
  (Polychromatic418967fa.accept_10_1_2_6_1_638 51 122 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 122 186 2 25 61 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 122 186 (accept_3_4 49 122 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 122 186 2 24 61 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 122 186 (Polychromatic418967fa.accept_9_2_5_6_1_536 47 122 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 122 186 2 23 61 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 122 186
  (Polychromatic418967fa.accept_12_9_2_6_1_455 45 122 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 122 186 2 22 61 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 122 186 (accept_3_4 43 122 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 122 186 2 21 61 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 122 186 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 122 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 122 186 2 20 61 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 122 186
  (Polychromatic418967fa.accept_9_3_5_6_1_253 39 122 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 122 186 2 19 61 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 122 186 (accept_3_4 37 122 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 122 186 2 18 61 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 122 186 (Polychromatic418967fa.accept_9_8_5_6_1_538 35 122 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 122 186 2 17 61 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 122 186
  (Polychromatic418967fa.accept_12_9_2_6_1_455 33 122 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 122 186 2 16 61 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 122 186 (accept_3_4 31 122 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 122 186 2 15 61 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 122 186 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 122 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 122 186 2 14 61 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 122 186
  (Polychromatic418967fa.accept_7_6_3_4_1_294 27 122 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 122 186 2 13 61 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 122 186 (accept_3_4 25 122 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 122 186 2 12 61 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 122 186 (Polychromatic418967fa.accept_13_10_5_4_1_3107 23 122 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 122 186 2 11 61 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 122 186
  (Polychromatic418967fa.accept_9_3_5_6_1_253 21 122 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 122 186 2 10 61 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 122 186 (accept_3_4 19 122 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 122 186 2 9 61 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 122 186 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 122 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 122 186 2 8 61 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 122 186 (Polychromatic418967fa.accept_7_1_3_4_1_128 15
  122 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 122 186 2 7 61 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 122 186 (accept_3_4 13
  122 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 122 186 2 6 61 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 122 186
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 122 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 122 186 2 5 61 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 122 186 (Polychromatic418967fa.accept_11_9_1_10_1_920 9 122 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 122 186 2 4 61 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 122 186 (accept_3_4 7 122 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 122 186 2 3 61 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 122 186 (Polychromatic418967fa.accept_23_5_7_2_1_10692 5 122 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 122 186 2 2 61 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 122 186 (Polychromatic418967fa.accept_9_3_5_6_1_253 3
  122 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 122 186 2 1 61 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 122 186 (accept_3_4 1
  122 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  186))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 121 186 (Eq.refl Bool.true)
  (allA_succ_of_accept 65 121 186 (accept_3_5 65 121 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 121 186 (Polychromatic418967fa.accept_9_1_4_6_1_5 64 121 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 121 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 121 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 121 186 (accept_3_5 62 121 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 121 186 (Polychromatic418967fa.accept_7_5_2_4_1_126 61 121 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 121 186
  (Polychromatic418967fa.accept_19_3_7_15_1_6419 60 121 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 121 186 (accept_3_5 59 121 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 121 186 (Polychromatic418967fa.accept_14_2_9_4_1_1735 58 121 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 121 186 (Polychromatic418967fa.accept_9_3_4_6_1_252 57 121 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 121 186 (accept_3_5 56 121 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 121 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 121 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 121 186
  (Polychromatic418967fa.accept_7_5_2_4_1_126 54 121 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 121 186 (accept_3_5 53 121 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 121 186 (Polychromatic418967fa.accept_9_7_4_6_1_273 52 121 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 121 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 121 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 121 186 (accept_3_5 50 121 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 121 186 (Polychromatic418967fa.accept_16_1_9_10_1_4740 49 121 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 121 186
  (Polychromatic418967fa.accept_7_6_2_4_1_291 48 121 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 121 186 (accept_3_5 47 121 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 121 186 (Polychromatic418967fa.accept_9_1_4_6_1_5 46 121 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 121 186 (Polychromatic418967fa.accept_10_5_1_6_1_672 45 121 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 121 186 (accept_3_5 44 121 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 121 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 121 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 121 186
  (Polychromatic418967fa.accept_10_2_1_6_1_634 42 121 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 121 186 (accept_3_5 41 121 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 121 186 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 121 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 121 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 121 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 121 186 (accept_3_5 38 121 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 121 186 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 121 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 121 186
  (Polychromatic418967fa.accept_19_17_7_15_1_6418 36 121 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 121 186 (accept_3_5 35 121 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 121 186 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 121 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 121 186 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 121 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 121 186 (accept_3_5 32 121 186
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 121 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 31
  121 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 121 186
  (Polychromatic418967fa.accept_9_3_4_6_1_252 30 121 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 121 186 (accept_3_5 29 121 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 121 186 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 121 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 121 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 121 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 121 186 (accept_3_5 26 121 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 121 186 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 121 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 121 186
  (Polychromatic418967fa.accept_15_9_1_6_1_657 24 121 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 121 186 (accept_3_5 23 121 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 121 186 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 121 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 121 186 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 121 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 121 186 (accept_3_5 20 121 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 121 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 121 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 121 186
  (Polychromatic418967fa.accept_15_3_1_6_1_206 18 121 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 121 186 (accept_3_5 17 121 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 121 186 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 121 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 121 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 121 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 121 186 (accept_3_5 14 121 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 121 186 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 121 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 121 186
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 121 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 121 186 (accept_3_5 11 121 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 121 186 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 121 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 121 186 (Polychromatic418967fa.accept_15_9_1_6_1_657 9 121 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 121 186 (accept_3_5 8 121 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 121 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 121 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 121 186
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 121 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 121 186 (accept_3_5 5 121 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  121 186 (Polychromatic418967fa.accept_22_4_11_10_1_10691 4 121 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 121 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 121 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 121 186 (accept_3_5 2 121 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 121 186 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 121 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 121
  186)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 120 186 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 120 186 6 11 20 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 120 186 (Polychromatic418967fa.accept_9_2_3_6_1_88 65 120 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 120 186 2 32 60 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 120 186 3 21 40 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 120 186 2 31 60 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 120 186
  (Polychromatic418967fa.accept_7_5_1_4_1_122 61 120 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 120 186 6 10 20 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 120 186 (Polychromatic418967fa.accept_7_3_1_4_1_121 59 120 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 120 186 2 29 60 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 120 186 3 19 40 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 120 186 2 28 60 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 120 186
  (Polychromatic418967fa.accept_9_1_3_6_1_70 55 120 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 120 186 6 9 20 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 120 186 (Polychromatic418967fa.accept_9_8_3_6_1_533 53 120 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 120 186 2 26 60 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 120 186 3 17 40 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 120 186 2 25 60 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 120 186
  (Polychromatic418967fa.accept_9_4_3_6_1_532 49 120 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 120 186 6 8 20 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 120 186 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 120 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 120 186 2 23 60 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 120 186 3 15 40 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 120 186 2 22 60 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 120 186
  (Polychromatic418967fa.accept_9_7_3_6_1_270 43 120 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 120 186 6 7 20 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 120 186 (Polychromatic418967fa.accept_9_5_3_6_1_269 41 120 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 120 186 2 20 60 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 120 186 3 13 40 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 120 186 2 19 60 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 120 186
  (Polychromatic418967fa.accept_9_1_3_6_1_70 37 120 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 120 186 6 6 20 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 120 186 (Polychromatic418967fa.accept_9_8_3_6_1_533 35 120 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 120 186 2 17 60 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 120 186 3 11 40 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 120 186 2 16 60 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 120 186
  (Polychromatic418967fa.accept_7_3_1_4_1_121 31 120 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 120 186 6 5 20 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 120 186 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 120 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 120 186 2 14 60 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 120 186 3 9 40 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 120 186 2 13 60 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 120 186
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 120 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 120 186 6 4 20 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 120 186 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 120 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 120 186 2 11 60 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 120 186 3 7 40 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 120 186 2 10 60 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 120 186
  (Polychromatic418967fa.accept_7_5_1_4_1_122 19 120 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 120 186 6 3 20 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 120 186 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 120 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 120 186 2 8 60 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 120 186 3 5 40 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 120 186 2 7 60 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 120 186 (Polychromatic418967fa.accept_9_4_3_6_1_532 13
  120 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 186 6 2 20 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 186
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 120 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 120 186 2 5 60 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 120 186 3 3 40 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 120 186 2 4 60 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 120 186 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 120 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120 186 6 1 20 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 120 186 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 120 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 120 186 2 2 60 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 120 186 3 1 40 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 120 186 2 1 60 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 120 186
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 120 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 120 186))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 119 186 (Eq.refl
  Bool.true) (allA_succ_of_accept 67 119 186 (accept_3_4 67 119 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 119 186 (Polychromatic418967fa.accept_9_3_2_6_1_264 66 119 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 119 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 119 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 119 186 (accept_3_4 64 119 186
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 119 186 (Polychromatic418967fa.accept_10_3_9_6_1_94
  63 119 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 119 186
  (Polychromatic418967fa.accept_9_8_2_6_1_875 62 119 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 119 186 (accept_3_4 61 119 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 119 186 (Polychromatic418967fa.accept_23_14_4_2_1_1181 60 119 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 119 186 (Polychromatic418967fa.accept_9_5_2_6_1_265 59 119 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 119 186 (accept_3_4 58 119 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 119 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 119 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 119 186
  (Polychromatic418967fa.accept_11_1_9_10_1_184 56 119 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 119 186 (accept_3_4 55 119 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 119 186 (Polychromatic418967fa.accept_15_9_14_6_1_3004 54 119 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 119 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 119 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 119 186 (accept_3_4 52 119 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 119 186 (Polychromatic418967fa.accept_13_12_2_4_1_3131 51 119 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 119 186
  (Polychromatic418967fa.accept_9_5_2_6_1_265 50 119 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 119 186 (accept_3_4 49 119 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 119 186 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 119 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 119 186 (Polychromatic418967fa.accept_19_9_5_15_1_2544 47 119 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 119 186 (accept_3_4 46 119 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 119 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 119 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 119 186
  (Polychromatic418967fa.accept_9_8_2_6_1_875 44 119 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 119 186 (accept_3_4 43 119 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 119 186 (Polychromatic418967fa.accept_19_4_5_15_1_2437 42 119 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 119 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 119 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 119 186 (accept_3_4 40 119 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 119 186 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 119 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 119 186
  (Polychromatic418967fa.accept_13_12_2_4_1_3131 38 119 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 119 186 (accept_3_4 37 119 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 119 186 (Polychromatic418967fa.accept_19_17_5_15_1_7921 36 119 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 119 186 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 119 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 119 186 (accept_3_4 34 119 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 119 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 119 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 119 186
  (Polychromatic418967fa.accept_9_5_2_6_1_265 32 119 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 119 186 (accept_3_4 31 119 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 119 186 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 119 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 119 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 119 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 119 186 (accept_3_4 28 119 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 119 186 (Polychromatic418967fa.accept_20_7_19_6_1_4742 27 119 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 119 186
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 119 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 119 186 (accept_3_4 25 119 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 119 186 (Polychromatic418967fa.accept_13_11_2_4_1_1590 24 119 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 119 186 (Polychromatic418967fa.accept_9_5_2_6_1_265 23 119 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 119 186 (accept_3_4 22 119 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 119 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 119 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 119 186
  (Polychromatic418967fa.accept_15_5_14_6_1_5120 20 119 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 119 186 (accept_3_4 19 119 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 119 186 (Polychromatic418967fa.accept_13_5_2_4_1_3955 18 119 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 119 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 119 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 119 186 (accept_3_4 16 119 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 119 186 (Polychromatic418967fa.accept_10_5_9_6_1_697 15 119 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 119 186
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 119 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 119 186 (accept_3_4 13 119 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 119 186 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 119 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 119 186 (Polychromatic418967fa.accept_13_11_2_4_1_1590 11 119 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 186 (accept_3_4 10 119 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 119 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 119 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 186
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 119 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 119 186 (accept_3_4 7 119 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  119 186 (Polychromatic418967fa.accept_13_6_2_4_1_923 6 119 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 119 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 119 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 186 (accept_3_4 4 119 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 119 186 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 119 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 186
  (Polychromatic418967fa.accept_24_2_23_18_1_3594 2 119 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 119 186 (accept_3_4 1 119 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  186)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 118 186 (Eq.refl Bool.true)
  (allA_succ_of_gcd 68 118 186 2 34 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 118 186 (Polychromatic418967fa.accept_9_4_1_6_1_284 67 118 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 118 186 2 33 59 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 118 186 (accept_3_5 65 118 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 118 186 2 32 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 118 186 (Polychromatic418967fa.accept_10_3_8_6_1_326
  63 118 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 118 186 2 31 59 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 118 186
  (Polychromatic418967fa.accept_7_5_6_4_1_117 61 118 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 118 186 2 30 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 118 186 (accept_3_5 59 118 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 118 186 2 29 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 118 186 (Polychromatic418967fa.accept_9_3_1_6_1_86 57 118 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 118 186 2 28 59 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 118 186
  (Polychromatic418967fa.accept_13_3_1_4_1_945 55 118 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 118 186 2 27 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 118 186 (accept_3_5 53 118 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 118 186 2 26 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 118 186 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 118 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 118 186 2 25 59 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 118 186
  (Polychromatic418967fa.accept_9_4_1_6_1_284 49 118 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 118 186 2 24 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 118 186 (accept_3_5 47 118 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 118 186 2 23 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 118 186 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 118 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 118 186 2 22 59 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 118 186
  (Polychromatic418967fa.accept_9_7_1_6_1_261 43 118 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 118 186 2 21 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 118 186 (accept_3_5 41 118 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 118 186 2 20 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 118 186 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 118 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 118 186 2 19 59 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 118 186
  (Polychromatic418967fa.accept_7_2_6_4_1_29 37 118 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 118 186 2 18 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 118 186 (accept_3_5 35 118 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 118 186 2 17 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 118 186 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 118 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 118 186 2 16 59 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 118 186
  (Polychromatic418967fa.accept_7_3_6_4_1_30 31 118 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 118 186 2 15 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 118 186 (accept_3_5 29 118 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 118 186 2 14 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 118 186 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 118 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 118 186 2 13 59 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 118 186
  (Polychromatic418967fa.accept_9_7_1_6_1_261 25 118 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 118 186 2 12 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 118 186 (accept_3_5 23 118 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 118 186 2 11 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 118 186 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 118 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 118 186 2 10 59 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 118 186
  (Polychromatic418967fa.accept_7_5_6_4_1_117 19 118 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 118 186 2 9 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 118 186 (accept_3_5 17 118 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  118 186 2 8 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 118 186 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 118 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 118 186 2 7 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 118 186 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 118 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 118 186 2 6 59 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 118 186 (accept_3_5 11 118 186
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 118 186 2 5 59 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 118 186
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 118 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 118 186 2 4 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 118 186 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 118 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 118 186 2 3 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 118 186 (accept_3_5 5 118 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 118 186 2 2 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 118 186 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 118 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 118 186 2 1 59 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 118 186 (Polychromatic418967fa.accept_19_1_4_15_1_2542
  1 118 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118
  186))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 117 186 (Eq.refl Bool.true)
  (allA_succ_of_gcd 69 117 186 3 23 39 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 117 186 (Polychromatic418967fa.accept_12_8_9_6_1_127 68 117 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 117 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 67
  117 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 117 186 3 22 39 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 117 186
  (Polychromatic418967fa.accept_7_2_5_4_1_115 65 117 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 117 186 (Polychromatic418967fa.accept_7_1_5_4_1_134 64 117 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 117 186 3 21 39 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 117 186 (Polychromatic418967fa.accept_7_6_5_4_1_297 62
  117 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 117 186
  (Polychromatic418967fa.accept_10_1_7_6_1_91 61 117 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 117 186 3 20 39 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 117 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 117 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 117 186 (Polychromatic418967fa.accept_7_2_5_4_1_115
  58 117 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 117 186 3 19 39 62
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 117 186
  (Polychromatic418967fa.accept_12_8_9_6_1_127 56 117 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 117 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 117 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 117 186 3 18 39 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 117 186 (Polychromatic418967fa.accept_10_3_7_6_1_659
  53 117 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 117 186
  (Polychromatic418967fa.accept_12_4_9_6_1_440 52 117 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 117 186 3 17 39 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 117 186 (Polychromatic418967fa.accept_7_1_5_4_1_134 50 117 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 117 186
  (Polychromatic418967fa.accept_18_13_9_6_1_4024 49 117 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 117 186 3 16 39 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 117 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 117 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 117 186
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 46 117 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 117 186 3 15 39 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 117 186 (Polychromatic418967fa.accept_7_2_5_4_1_115 44 117 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 43
  117 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 117 186 3 14 39 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 117 186
  (Polychromatic418967fa.accept_7_6_5_4_1_297 41 117 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 117 186 (Polychromatic418967fa.accept_12_4_9_6_1_440 40 117 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 117 186 3 13 39 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 117 186 (Polychromatic418967fa.accept_12_2_9_6_1_439
  38 117 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 186
  (Polychromatic418967fa.accept_7_2_5_4_1_115 37 117 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 117 186 3 12 39 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 117 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 117 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 186 (Polychromatic418967fa.accept_7_6_5_4_1_297
  34 117 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 117 186 3 11 39 62
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 117 186
  (Polychromatic418967fa.accept_12_8_9_6_1_127 32 117 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 117 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 117 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 117 186 3 10 39 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 117 186 (Polychromatic418967fa.accept_7_1_5_4_1_134 29
  117 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 186
  (Polychromatic418967fa.accept_12_4_9_6_1_440 28 117 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 117 186 3 9 39 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 117 186 (Polychromatic418967fa.accept_12_2_9_6_1_439 26 117 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 186 (Polychromatic418967fa.accept_11_3_7_10_1_180 25 117
  186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 117 186 3 8 39 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 117 186
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 117 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 117 186 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 117 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 117 186 3 7 39 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 117 186 (Polychromatic418967fa.accept_7_6_5_4_1_297 20
  117 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 186
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 117 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 117 186 3 6 39 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 117 186 (Polychromatic418967fa.accept_15_2_12_6_1_3063 17 117 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 186 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 117 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 117 186 3 5 39 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 117 186
  (Polychromatic418967fa.accept_11_3_7_10_1_180 14 117 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 117 186 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 117 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 117 186 3 4 39 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 117 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 11
  117 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 186
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 117 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 117 186 3 3 39 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 117 186 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 117 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 117 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 117 186 3 2 39 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 117 186
  (Polychromatic418967fa.accept_15_5_12_6_1_639 5 117 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 117 186 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 117 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 117 186 3 1 39 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 117 186 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 117 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 186
  (Polychromatic418967fa.accept_7_1_5_4_1_134 1 117 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 117 186)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 116 186
  (Eq.refl Bool.true) (allA_succ_of_gcd 70 116 186 2 35 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 116 186 (Polychromatic418967fa.accept_12_9_8_6_1_466 69 116 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 116 186 2 34 58 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 116 186 (accept_3_4 67
  116 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 116 186 2 33 58 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 116 186
  (Polychromatic418967fa.accept_9_2_8_6_1_79 65 116 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 116 186 2 32 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 116 186 (Polychromatic418967fa.accept_12_3_8_6_1_895 63 116 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 116 186 2 31 58 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 116 186 (accept_3_4 61 116 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 116 186 2 30 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 116 186 (Polychromatic418967fa.accept_9_5_8_6_1_281 59
  116 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 116 186 2 29 58 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 116 186
  (Polychromatic418967fa.accept_9_3_8_6_1_80 57 116 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 116 186 2 28 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 116 186 (accept_3_4 55 116 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 116 186 2 27 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 116 186 (Polychromatic418967fa.accept_17_2_14_16_1_2187 53 116 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 116 186 2 26 58 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 116 186
  (Polychromatic418967fa.accept_12_3_8_6_1_895 51 116 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 116 186 2 25 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 116 186 (accept_3_4 49 116 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 116 186 2 24 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 116 186 (Polychromatic418967fa.accept_9_2_8_6_1_79 47 116 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 116 186 2 23 58 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 116 186
  (Polychromatic418967fa.accept_12_9_8_6_1_466 45 116 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 116 186 2 22 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 116 186 (accept_3_4 43 116 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 116 186 2 21 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 116 186 (Polychromatic418967fa.accept_9_5_8_6_1_281 41 116 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 116 186 2 20 58 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 116 186
  (Polychromatic418967fa.accept_9_3_8_6_1_80 39 116 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 116 186 2 19 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 116 186 (accept_3_4 37 116 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 116 186 2 18 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 116 186 (Polychromatic418967fa.accept_15_5_11_6_1_692 35 116 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 116 186 2 17 58 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 116 186
  (Polychromatic418967fa.accept_12_9_8_6_1_466 33 116 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 116 186 2 16 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 116 186 (accept_3_4 31 116 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 116 186 2 15 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 116 186 (Polychromatic418967fa.accept_9_2_8_6_1_79 29 116 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 116 186 2 14 58 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 116 186
  (Polychromatic418967fa.accept_11_5_6_10_1_1432 27 116 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 116 186 2 13 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 116 186 (accept_3_4 25 116 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 116 186 2 12 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 116 186 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 116 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 116 186 2 11 58 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 116 186
  (Polychromatic418967fa.accept_9_3_8_6_1_80 21 116 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 116 186 2 10 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 116 186 (accept_3_4 19 116 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 116 186 2 9 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 116 186 (Polychromatic418967fa.accept_15_2_11_6_1_2135 17 116 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 116 186 2 8 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 116 186 (Polychromatic418967fa.accept_12_3_8_6_1_895
  15 116 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 116 186 2 7 58 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 116 186
  (accept_3_4 13 116 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 116 186 2 6 58 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 116 186
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 116 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 116 186 2 5 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 116 186 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 116 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 116 186 2 4 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 116 186 (accept_3_4 7 116 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 116 186 2 3 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 116 186 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 116 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 116 186 2 2 58 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 116 186 (Polychromatic418967fa.accept_9_3_8_6_1_80 3
  116 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 116 186 2 1 58 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 116 186 (accept_3_4 1
  116 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  186))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 115 186 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 115 186 (accept_3_5 71 115 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 115 186 (Polychromatic418967fa.accept_11_4_5_10_1_926 70 115 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 115 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 115 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 115 186 (accept_3_5 68 115 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 115 186 (Polychromatic418967fa.accept_9_4_7_6_1_255 67 115 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 115 186
  (Polychromatic418967fa.accept_9_3_7_6_1_76 66 115 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 115 186 (accept_3_5 65 115 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 115 186 (Polychromatic418967fa.accept_7_1_3_4_1_128 64 115 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 115 186 (Polychromatic418967fa.accept_14_7_3_4_1_1816 63 115 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 115 186 (accept_3_5 62 115 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 115 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 115 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 115 186
  (Polychromatic418967fa.accept_13_8_11_4_1_1553 60 115 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 115 186 (accept_3_5 59 115 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 115 186 (Polychromatic418967fa.accept_9_4_7_6_1_255 58 115 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 115 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 115 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 115 186 (accept_3_5 56 115 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 115 186 (Polychromatic418967fa.accept_7_6_3_4_1_294 55 115 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 115 186
  (Polychromatic418967fa.accept_10_4_5_6_1_651 54 115 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 115 186 (accept_3_5 53 115 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 115 186 (Polychromatic418967fa.accept_19_14_1_15_1_7914 52 115 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 115 186 (Polychromatic418967fa.accept_10_1_5_6_1_649 51 115 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 115 186 (accept_3_5 50 115 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 115 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 115 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 115 186
  (Polychromatic418967fa.accept_7_6_3_4_1_294 48 115 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 115 186 (accept_3_5 47 115 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 115 186 (Polychromatic418967fa.accept_9_1_7_6_1_75 46 115 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 115 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 115 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 115 186 (accept_3_5 44 115 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 115 186 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 115 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 115 186
  (Polychromatic418967fa.accept_15_12_10_6_1_2134 42 115 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 115 186 (accept_3_5 41 115 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 115 186 (Polychromatic418967fa.accept_9_4_7_6_1_255 40 115 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 115 186 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 115 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 115 186 (accept_3_5 38 115 186
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 115 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 37
  115 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 115 186
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 115 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 115 186 (accept_3_5 35 115 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 115 186 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 115 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 115 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 115 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 115 186 (accept_3_5 32 115 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 115 186 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 115 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 115 186
  (Polychromatic418967fa.accept_9_3_7_6_1_76 30 115 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 115 186 (accept_3_5 29 115 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 115 186 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 115 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 115 186 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 115 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 115 186 (accept_3_5 26 115 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 115 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 115 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 115 186
  (Polychromatic418967fa.accept_10_4_5_6_1_651 24 115 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 115 186 (accept_3_5 23 115 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 115 186 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 115 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 115 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 115 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 115 186 (accept_3_5 20 115 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 115 186 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 115 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 115 186
  (Polychromatic418967fa.accept_15_3_10_6_1_632 18 115 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 115 186 (accept_3_5 17 115 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 115 186 (Polychromatic418967fa.accept_15_1_10_6_1_631 16 115 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 115 186 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 115 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 115 186 (accept_3_5 14 115 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 115 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 115 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 115 186
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 115 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 115 186 (accept_3_5 11 115 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 115 186 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 115 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 115 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 115 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 115 186 (accept_3_5 8 115 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 115 186 (Polychromatic418967fa.accept_13_7_11_4_1_2247 7 115 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 115 186
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 115 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 115 186 (accept_3_5 5 115 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  115 186 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 115 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 115 186 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 115 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 186 (accept_3_5 2 115 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 115 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 115 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115
  186)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 114 186 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 114 186 6 12 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 114 186 (Polychromatic418967fa.accept_11_5_4_10_1_524 71 114 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 114 186 2 35 57 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 114 186 3 23 38 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 114 186 2 34 57 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 114 186
  (Polychromatic418967fa.accept_21_4_9_18_1_6001 67 114 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 114 186 6 11 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 114 186 (Polychromatic418967fa.accept_10_5_4_6_1_319 65 114 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 114 186 2 32 57 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 114 186 3 21 38 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 114 186 2 31 57 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 114 186
  (Polychromatic418967fa.accept_7_5_2_4_1_126 61 114 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 114 186 6 10 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 114 186 (Polychromatic418967fa.accept_13_7_10_4_1_919 59 114 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 114 186 2 29 57 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 114 186 3 19 38 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 114 186 2 28 57 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 114 186
  (Polychromatic418967fa.accept_7_6_2_4_1_291 55 114 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 114 186 6 9 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 114 186 (Polychromatic418967fa.accept_13_1_10_4_1_954 53 114 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 114 186 2 26 57 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 114 186 3 17 38 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 114 186 2 25 57 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 114 186
  (Polychromatic418967fa.accept_11_5_4_10_1_524 49 114 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 114 186 6 8 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 114 186 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 114 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 114 186 2 23 57 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 114 186 3 15 38 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 114 186 2 22 57 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 114 186
  (Polychromatic418967fa.accept_21_1_9_18_1_4428 43 114 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 114 186 6 7 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 114 186 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 114 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 114 186 2 20 57 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 114 186 3 13 38 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 114 186 2 19 57 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 114 186
  (Polychromatic418967fa.accept_13_11_10_4_1_1565 37 114 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 114 186 6 6 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 114 186 (Polychromatic418967fa.accept_10_5_4_6_1_319 35 114 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 114 186 2 17 57 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 114 186 3 11 38 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 114 186 2 16 57 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 114 186
  (Polychromatic418967fa.accept_13_5_10_4_1_1564 31 114 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 114 186 6 5 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 114 186 (Polychromatic418967fa.accept_15_14_9_6_1_5093 29 114 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 114 186 2 14 57 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 114 186 3 9 38 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 114 186 2 13 57 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 114 186
  (Polychromatic418967fa.accept_10_5_4_6_1_319 25 114 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 114 186 6 4 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 114 186 (Polychromatic418967fa.accept_14_9_2_4_1_1814 23 114 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 114 186 2 11 57 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 114 186 3 7 38 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 114 186 2 10 57 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 114 186
  (Polychromatic418967fa.accept_7_5_2_4_1_126 19 114 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 186 6 3 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 114 186 (Polychromatic418967fa.accept_21_17_9_18_1_7521 17 114 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 114 186 2 8 57 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 114 186 3 5 38 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 114 186 2 7 57 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 114 186
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 114 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 114 186 6 2 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 114 186 (Polychromatic418967fa.accept_13_11_10_4_1_1565 11 114 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 114 186 2 5 57 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 114 186 3 3 38 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 114 186 2 4 57 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 114 186
  (Polychromatic418967fa.accept_13_7_10_4_1_919 7 114 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 114 186 6 1 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 114 186 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 114 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 114 186 2 2 57 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 114 186 3 1 38 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 114 186 2 1 57 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 186 (Polychromatic418967fa.accept_13_1_10_4_1_954 1 114 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  186))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 113 186 (Eq.refl
  Bool.true) (allA_succ_of_accept 73 113 186 (accept_3_4 73 113 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 113 186 (Polychromatic418967fa.accept_13_7_9_4_1_918 72 113 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 113 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 113 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 113 186 (accept_3_4 70 113 186
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 113 186 (Polychromatic418967fa.accept_10_9_3_6_1_686
  69 113 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 113 186
  (Polychromatic418967fa.accept_7_5_1_4_1_122 68 113 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 113 186 (accept_3_4 67 113 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 113 186 (Polychromatic418967fa.accept_7_3_1_4_1_121 66 113 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 113 186 (Polychromatic418967fa.accept_9_2_5_6_1_536 65 113 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 113 186 (accept_3_4 64 113 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 113 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 113 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 113 186
  (Polychromatic418967fa.accept_9_8_5_6_1_538 62 113 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 113 186 (accept_3_4 61 113 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 113 186 (Polychromatic418967fa.accept_13_8_9_4_1_1552 60 113 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 113 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 113 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 113 186 (accept_3_4 58 113 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 113 186 (Polychromatic418967fa.accept_9_3_5_6_1_253 57 113 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 113 186
  (Polychromatic418967fa.accept_9_2_5_6_1_536 56 113 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 113 186 (accept_3_4 55 113 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 113 186 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 113 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 113 186 (Polychromatic418967fa.accept_9_8_5_6_1_538 53 113 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 113 186 (accept_3_4 52 113 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 113 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 113 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 113 186
  (Polychromatic418967fa.accept_19_12_18_15_1_10690 50 113 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 113 186 (accept_3_4 49 113 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 113 186 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 113 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 113 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 113 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 113 186 (accept_3_4 46 113 186
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 113 186 (Polychromatic418967fa.accept_7_3_1_4_1_121
  45 113 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 113 186
  (Polychromatic418967fa.accept_9_8_5_6_1_538 44 113 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 113 186 (accept_3_4 43 113 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 113 186 (Polychromatic418967fa.accept_19_4_18_15_1_7899 42 113 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 113 186 (Polychromatic418967fa.accept_16_9_1_10_1_3610 41 113 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 113 186 (accept_3_4 40 113 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 113 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 113 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 113 186
  (Polychromatic418967fa.accept_7_3_1_4_1_121 38 113 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 113 186 (accept_3_4 37 113 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 113 186 (Polychromatic418967fa.accept_21_15_8_18_1_10689 36 113 186 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 35 113 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 113 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 113 186 (accept_3_4 34 113 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 113 186 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 113 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 113 186
  (Polychromatic418967fa.accept_13_6_9_4_1_2288 32 113 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 113 186 (accept_3_4 31 113 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 113 186 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 113 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 113 186 (Polychromatic418967fa.accept_9_2_5_6_1_536 29 113 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 113 186 (accept_3_4 28 113 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 113 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 113 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 113 186
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 113 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 113 186 (accept_3_4 25 113 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 113 186 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 113 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 113 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 113 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 113 186 (accept_3_4 22 113 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 113 186 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 113 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 186
  (Polychromatic418967fa.accept_9_2_5_6_1_536 20 113 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 113 186 (accept_3_4 19 113 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 113 186 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 113 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 113 186 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 113 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 186 (accept_3_4 16 113 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 113 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 113 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 186
  (Polychromatic418967fa.accept_15_14_8_6_1_2133 14 113 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 113 186 (accept_3_4 13 113 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 113 186 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 113 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 113 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 113 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 186 (accept_3_4 10 113 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 186 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 113 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 186
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 113 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 113 186 (accept_3_4 7 113 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  113 186 (Polychromatic418967fa.accept_13_6_9_4_1_2288 6 113 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 113 186 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 113 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 186 (accept_3_4 4 113 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 113 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 186
  (Polychromatic418967fa.accept_9_2_5_6_1_536 2 113 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 186 (accept_3_4 1 113 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  186)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 112 186 (Eq.refl
  Bool.true) (allA_succ_of_gcd 74 112 186 2 37 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 112 186 (Polychromatic418967fa.accept_9_1_4_6_1_5 73 112 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 112 186 2 36 56 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 112 186 (accept_3_5 71 112 186
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 112 186 2 35 56 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 112 186
  (Polychromatic418967fa.accept_12_9_4_6_1_460 69 112 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 112 186 2 34 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 112 186 (Polychromatic418967fa.accept_11_1_2_10_1_1426 67 112 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 112 186 2 33 56 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 112 186 (accept_3_5 65 112 186
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 112 186 2 32 56 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 112 186
  (Polychromatic418967fa.accept_12_3_4_6_1_434 63 112 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 112 186 2 31 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 112 186 (Polychromatic418967fa.accept_9_7_4_6_1_273 61 112 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 112 186 2 30 56 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 112 186 (accept_3_5 59 112 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 112 186 2 29 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 112 186 (Polychromatic418967fa.accept_9_3_4_6_1_252 57
  112 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 112 186 2 28 56 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 112 186
  (Polychromatic418967fa.accept_9_1_4_6_1_5 55 112 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 112 186 2 27 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 112 186 (accept_3_5 53 112 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 112 186 2 26 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 112 186 (Polychromatic418967fa.accept_10_1_2_6_1_638 51 112 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 112 186 2 25 56 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 112 186
  (Polychromatic418967fa.accept_13_10_8_4_1_3098 49 112 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 112 186 2 24 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 112 186 (accept_3_5 47 112 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 112 186 2 23 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 112 186 (Polychromatic418967fa.accept_11_1_2_10_1_1426 45 112 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 112 186 2 22 56 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 112 186
  (Polychromatic418967fa.accept_9_7_4_6_1_273 43 112 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 112 186 2 21 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 112 186 (accept_3_5 41 112 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 112 186 2 20 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 112 186 (Polychromatic418967fa.accept_9_3_4_6_1_252 39 112 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 112 186 2 19 56 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 112 186
  (Polychromatic418967fa.accept_9_1_4_6_1_5 37 112 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 112 186 2 18 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 112 186 (accept_3_5 35 112 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 112 186 2 17 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 112 186 (Polychromatic418967fa.accept_12_9_4_6_1_460 33 112 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 112 186 2 16 56 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 112 186
  (Polychromatic418967fa.accept_10_1_2_6_1_638 31 112 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 112 186 2 15 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 112 186 (accept_3_5 29 112 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 112 186 2 14 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 112 186 (Polychromatic418967fa.accept_12_3_4_6_1_434 27 112 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 112 186 2 13 56 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 112 186
  (Polychromatic418967fa.accept_9_7_4_6_1_273 25 112 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 112 186 2 12 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 112 186 (accept_3_5 23 112 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 112 186 2 11 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 112 186 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 112 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 112 186 2 10 56 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 112 186
  (Polychromatic418967fa.accept_9_1_4_6_1_5 19 112 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 112 186 2 9 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 112 186 (accept_3_5 17 112 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  112 186 2 8 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 112 186 (Polychromatic418967fa.accept_12_3_4_6_1_434 15 112 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 112 186 2 7 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 112 186 (Polychromatic418967fa.accept_15_13_7_6_1_682 13 112 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 112 186 2 6 56 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 112 186 (accept_3_5 11 112 186
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 112 186 2 5 56 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 112 186
  (Polychromatic418967fa.accept_12_9_4_6_1_460 9 112 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 112 186 2 4 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 112 186 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 112 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 112 186 2 3 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 112 186 (accept_3_5 5 112 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 112 186 2 2 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 112 186 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 112 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 112 186 2 1 56 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 112 186 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 112
  186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112
  186))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76 111 186 (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 111 186 3 25 37 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 74 111 186 (Polychromatic418967fa.accept_9_2_3_6_1_88 74 111 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 111 186
  (Polychromatic418967fa.accept_4_1_3_2_1_3 73 111 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 111 186 3 24 37 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 111 186 (Polychromatic418967fa.accept_9_8_3_6_1_533 71 111 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 111 186 (Polychromatic418967fa.accept_9_7_3_6_1_270
  70 111 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 111 186 3 23 37 62
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 111 186
  (Polychromatic418967fa.accept_7_5_6_4_1_117 68 111 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 111 186 (Polychromatic418967fa.accept_9_4_3_6_1_532 67 111 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 111 186 3 22 37 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 111 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 65
  111 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 111 186
  (Polychromatic418967fa.accept_9_1_3_6_1_70 64 111 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 111 186 3 21 37 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 111 186 (Polychromatic418967fa.accept_9_8_3_6_1_533 62 111 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 111 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 61
  111 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 111 186 3 20 37 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 111 186
  (Polychromatic418967fa.accept_7_3_6_4_1_30 59 111 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 111 186 (Polychromatic418967fa.accept_7_2_6_4_1_29 58 111 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 111 186 3 19 37 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 111 186 (Polychromatic418967fa.accept_9_2_3_6_1_88 56
  111 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 186
  (Polychromatic418967fa.accept_9_1_3_6_1_70 55 111 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 111 186 3 18 37 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 111 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 111 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 111 186 (Polychromatic418967fa.accept_7_3_6_4_1_30 52
  111 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 111 186 3 17 37 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 111 186
  (Polychromatic418967fa.accept_9_5_3_6_1_269 50 111 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 111 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 111 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 111 186 3 16 37 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 111 186 (Polychromatic418967fa.accept_7_5_6_4_1_117 47
  111 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 111 186
  (Polychromatic418967fa.accept_9_1_3_6_1_70 46 111 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 111 186 3 15 37 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 111 186 (Polychromatic418967fa.accept_7_2_6_4_1_29 44 111 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 186 (Polychromatic418967fa.accept_9_7_3_6_1_270
  43 111 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 111 186 3 14 37 62
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 111 186
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 111 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 111 186 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 111 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 111 186 3 13 37 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 111 186 (Polychromatic418967fa.accept_7_3_6_4_1_30 38
  111 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 186
  (Polychromatic418967fa.accept_4_1_3_2_1_3 37 111 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 111 186 3 12 37 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 111 186 (Polychromatic418967fa.accept_9_8_3_6_1_533 35 111 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 111 186 (Polychromatic418967fa.accept_9_7_3_6_1_270
  34 111 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 111 186 3 11 37 62
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 111 186
  (Polychromatic418967fa.accept_9_5_3_6_1_269 32 111 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 111 186 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 111 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 111 186 3 10 37 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 111 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 29
  111 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 186
  (Polychromatic418967fa.accept_9_1_3_6_1_70 28 111 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 111 186 3 9 37 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 111 186 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 111 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 111 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 111 186 3 8 37 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 111 186
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 111 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 111 186 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 111 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 111 186 3 7 37 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 111 186 (Polychromatic418967fa.accept_9_2_3_6_1_88 20
  111 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 186
  (Polychromatic418967fa.accept_7_5_6_4_1_117 19 111 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 111 186 3 6 37 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 111 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 111 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 186 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 111 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 111 186 3 5 37 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 111 186
  (Polychromatic418967fa.accept_9_5_3_6_1_269 14 111 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 111 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 111 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 111 186 3 4 37 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 111 186 (Polychromatic418967fa.accept_9_2_3_6_1_88 11
  111 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 186
  (Polychromatic418967fa.accept_7_3_6_4_1_30 10 111 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 111 186 3 3 37 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 111 186 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 111 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 186 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 111 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 111 186 3 2 37 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 111 186
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 111 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 111 186 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 111 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 111 186 3 1 37 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 111 186 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 111 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 186
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 111 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 111 186)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 110 186
  (Eq.refl Bool.true) (allA_succ_of_gcd 76 110 186 2 38 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 110 186 (Polychromatic418967fa.accept_9_3_2_6_1_264 75 110 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 110 186 2 37 55 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 110 186 (accept_3_4 73
  110 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 110 186 2 36 55 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 110 186
  (Polychromatic418967fa.accept_7_1_5_4_1_134 71 110 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 110 186 2 35 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 110 186 (Polychromatic418967fa.accept_7_6_5_4_1_297 69 110 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 110 186 2 34 55 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 110 186 (accept_3_4 67 110 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 110 186 2 33 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 110 186 (Polychromatic418967fa.accept_7_2_5_4_1_115 65
  110 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 110 186 2 32 55 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 110 186
  (Polychromatic418967fa.accept_12_3_2_6_1_138 63 110 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 110 186 2 31 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 110 186 (accept_3_4 61 110 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 110 186 2 30 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 110 186 (Polychromatic418967fa.accept_9_5_2_6_1_265 59 110 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 110 186 2 29 55 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 110 186
  (Polychromatic418967fa.accept_7_1_5_4_1_134 57 110 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 110 186 2 28 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 110 186 (accept_3_4 55 110 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 110 186 2 27 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 110 186 (Polychromatic418967fa.accept_9_8_2_6_1_875 53 110 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 110 186 2 26 55 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 110 186
  (Polychromatic418967fa.accept_7_2_5_4_1_115 51 110 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 110 186 2 25 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 110 186 (accept_3_4 49 110 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 110 186 2 24 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 110 186 (Polychromatic418967fa.accept_16_15_14_10_1_9549 47 110 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 110 186 2 23 55 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 110 186
  (Polychromatic418967fa.accept_12_9_2_6_1_455 45 110 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 110 186 2 22 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 110 186 (accept_3_4 43 110 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 110 186 2 21 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 110 186 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 110 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 110 186 2 20 55 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 110 186
  (Polychromatic418967fa.accept_9_3_2_6_1_264 39 110 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 110 186 2 19 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 110 186 (accept_3_4 37 110 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 110 186 2 18 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 110 186 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 110 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 110 186 2 17 55 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 110 186
  (Polychromatic418967fa.accept_12_9_2_6_1_455 33 110 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 110 186 2 16 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 110 186 (accept_3_4 31 110 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 110 186 2 15 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 110 186 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 110 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 110 186 2 14 55 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 110 186
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 110 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 110 186 2 13 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 110 186 (accept_3_4 25 110 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 110 186 2 12 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 110 186 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 110 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 110 186 2 11 55 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 110 186
  (Polychromatic418967fa.accept_9_3_2_6_1_264 21 110 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 110 186 2 10 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 110 186 (accept_3_4 19 110 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 110 186 2 9 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 110 186 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 110 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 110 186 2 8 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 110 186 (Polychromatic418967fa.accept_7_1_5_4_1_134 15
  110 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 110 186 2 7 55 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 110 186 (accept_3_4 13
  110 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 110 186 2 6 55 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 110 186
  (Polychromatic418967fa.accept_13_11_6_4_1_3121 11 110 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 110 186 2 5 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 110 186 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 110 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 110 186 2 4 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 110 186 (accept_3_4 7 110 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 110 186 2 3 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 110 186 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 110 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 110 186 2 2 55 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 110 186 (Polychromatic418967fa.accept_9_3_2_6_1_264 3
  110 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 110 186 2 1 55 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 110 186 (accept_3_4 1
  110 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  186))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 78 109 186 (Eq.refl
  Bool.true) (allA_succ_of_accept 77 109 186 (accept_3_5 77 109 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 109 186 (Polychromatic418967fa.accept_9_4_1_6_1_284 76 109 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 109 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 109 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 109 186 (accept_3_5 74 109 186
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 109 186 (Polychromatic418967fa.accept_10_3_9_6_1_94
  73 109 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 109 186
  (Polychromatic418967fa.accept_21_9_4_18_1_7615 72 109 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 109 186 (accept_3_5 71 109 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 109 186 (Polychromatic418967fa.accept_9_7_1_6_1_261 70 109 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 109 186 (Polychromatic418967fa.accept_15_9_4_6_1_3075 69 109 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 109 186 (accept_3_5 68 109 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 109 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 109 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 109 186
  (Polychromatic418967fa.accept_9_3_1_6_1_86 66 109 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 109 186 (accept_3_5 65 109 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 109 186 (Polychromatic418967fa.accept_13_12_5_4_1_3133 64 109 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 109 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 109 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 109 186 (accept_3_5 62 109 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 109 186 (Polychromatic418967fa.accept_9_7_1_6_1_261 61 109 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 109 186
  (Polychromatic418967fa.accept_16_12_13_10_1_2637 60 109 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 109 186 (accept_3_5 59 109 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 109 186 (Polychromatic418967fa.accept_9_4_1_6_1_284 58 109 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 109 186 (Polychromatic418967fa.accept_9_3_1_6_1_86 57 109 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 109 186 (accept_3_5 56 109 186
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 109 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 55
  109 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 109 186
  (Polychromatic418967fa.accept_13_2_5_4_1_3926 54 109 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 109 186 (accept_3_5 53 109 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 109 186 (Polychromatic418967fa.accept_9_7_1_6_1_261 52 109 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 109 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 109 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 109 186 (accept_3_5 50 109 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 109 186 (Polychromatic418967fa.accept_9_4_1_6_1_284 49 109 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 109 186
  (Polychromatic418967fa.accept_9_3_1_6_1_86 48 109 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 109 186 (accept_3_5 47 109 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 109 186 (Polychromatic418967fa.accept_16_14_13_10_1_2624 46 109 186 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 109 186 (Polychromatic418967fa.accept_10_5_9_6_1_697 45 109 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 109 186 (accept_3_5 44 109 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 109 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 109 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 109 186
  (Polychromatic418967fa.accept_17_8_7_16_1_9508 42 109 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 109 186 (accept_3_5 41 109 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 109 186 (Polychromatic418967fa.accept_9_4_1_6_1_284 40 109 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 109 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 109 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 109 186 (accept_3_5 38 109 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 109 186 (Polychromatic418967fa.accept_16_5_13_10_1_3664 37 109 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 109 186
  (Polychromatic418967fa.accept_13_10_5_4_1_3107 36 109 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 109 186 (accept_3_5 35 109 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 109 186 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 109 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 109 186 (Polychromatic418967fa.accept_10_3_9_6_1_94 33 109 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 109 186 (accept_3_5 32 109 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 109 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 109 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 109 186
  (Polychromatic418967fa.accept_9_3_1_6_1_86 30 109 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 109 186 (accept_3_5 29 109 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 109 186 (Polychromatic418967fa.accept_13_2_5_4_1_3926 28 109 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 109 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 109 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 109 186 (accept_3_5 26 109 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 109 186 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 109 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 109 186
  (Polychromatic418967fa.accept_15_9_4_6_1_3075 24 109 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 109 186 (accept_3_5 23 109 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 109 186 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 109 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 109 186 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 109 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 109 186 (accept_3_5 20 109 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 109 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 109 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 109 186
  (Polychromatic418967fa.accept_19_18_14_15_1_9277 18 109 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 109 186 (accept_3_5 17 109 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 109 186 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 109 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 109 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 109 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 109 186 (accept_3_5 14 109 186
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 109 186 (Polychromatic418967fa.accept_9_4_1_6_1_284
  13 109 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 109 186
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 109 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 109 186 (accept_3_5 11 109 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 109 186 (Polychromatic418967fa.accept_13_10_5_4_1_3107 10 109 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 109 186 (Polychromatic418967fa.accept_13_9_5_4_1_1591 9 109 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 109 186 (accept_3_5 8 109 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 109 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 109 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 109 186
  (Polychromatic418967fa.accept_13_6_5_4_1_3924 6 109 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 109 186 (accept_3_5 5 109 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  109 186 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 109 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 109 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 109 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 109 186 (accept_3_5 2 109 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 109 186 (Polychromatic418967fa.accept_13_1_5_4_1_463 1 109 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 109
  186)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 79 108 186 (Eq.refl
  Bool.true) (allA_succ_of_gcd 78 108 186 6 13 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 108 186 (Polychromatic418967fa.accept_14_7_10_4_1_130 77 108 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 108 186 2 38 54 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 108 186 3 25 36 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 108 186 2 37 54 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 108 186
  (Polychromatic418967fa.accept_10_3_8_6_1_326 73 108 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 108 186 6 12 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 108 186 (Polychromatic418967fa.accept_7_1_3_4_1_128 71 108 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 108 186 2 35 54 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 108 186 3 23 36 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 108 186 2 34 54 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 108 186
  (Polychromatic418967fa.accept_11_1_9_10_1_184 67 108 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 108 186 6 11 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 108 186 (Polychromatic418967fa.accept_15_5_3_6_1_2128 65 108 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 108 186 2 32 54 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 108 186 3 21 36 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 108 186 2 31 54 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 108 186
  (Polychromatic418967fa.accept_15_1_3_6_1_621 61 108 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 108 186 6 10 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 108 186 (Polychromatic418967fa.accept_16_11_12_10_1_3641 59 108 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 108 186 2 29 54 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 108 186 3 19 36 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 108 186 2 28 54 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 108 186
  (Polychromatic418967fa.accept_7_6_3_4_1_294 55 108 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 108 186 6 9 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 108 186 (Polychromatic418967fa.accept_10_3_8_6_1_326 53 108 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 108 186 2 26 54 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 108 186 3 17 36 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 108 186 2 25 54 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 108 186
  (Polychromatic418967fa.accept_14_7_10_4_1_130 49 108 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 108 186 6 8 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 108 186 (Polychromatic418967fa.accept_19_9_13_15_1_3677 47 108 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 108 186 2 23 54 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 108 186 3 15 36 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 108 186 2 22 54 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 108 186
  (Polychromatic418967fa.accept_7_1_3_4_1_128 43 108 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 108 186 6 7 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 108 186 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 108 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 108 186 2 20 54 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 108 186 3 13 36 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 108 186 2 19 54 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 108 186
  (Polychromatic418967fa.accept_16_5_12_10_1_3508 37 108 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 108 186 6 6 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 108 186 (Polychromatic418967fa.accept_14_7_10_4_1_130 35 108 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 108 186 2 17 54 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 108 186 3 11 36 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 108 186 2 16 54 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 108 186
  (Polychromatic418967fa.accept_15_1_3_6_1_621 31 108 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 108 186 6 5 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 108 186 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 108 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 108 186 2 14 54 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 108 186 3 9 36 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 108 186 2 13 54 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 108 186
  (Polychromatic418967fa.accept_15_10_3_6_1_3042 25 108 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 108 186 6 4 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 108 186 (Polychromatic418967fa.accept_10_3_8_6_1_326 23 108 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 108 186 2 11 54 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 108 186 3 7 36 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 108 186 2 10 54 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 108 186
  (Polychromatic418967fa.accept_11_8_9_10_1_503 19 108 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 108 186 6 3 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 108 186 (Polychromatic418967fa.accept_19_17_13_15_1_1402 17 108 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 108 186 2 8 54 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 108 186 3 5 36 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 108 186 2 7 54 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 108 186
  (Polychromatic418967fa.accept_7_6_3_4_1_294 13 108 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 108 186 6 2 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 108 186 (Polychromatic418967fa.accept_15_11_3_6_1_1306 11 108 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 108 186 2 5 54 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 108 186 3 3 36 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 108 186 2 4 54 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 108 186 (Polychromatic418967fa.accept_14_7_10_4_1_130 7
  108 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 186 6 1 18 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 186
  (Polychromatic418967fa.accept_15_5_3_6_1_2128 5 108 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 108 186 2 2 54 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 108 186 3 1 36 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 108 186 2 1 54 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 108 186 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 108 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 108
  186))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 107 186 (Eq.refl
  Bool.true) (allA_succ_of_accept 79 107 186 (accept_3_4 79 107 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 107 186 (Polychromatic418967fa.accept_21_15_2_18_1_1815 78 107 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 107 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 77
  107 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 107 186 (accept_3_4 76
  107 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 107 186
  (Polychromatic418967fa.accept_7_5_2_4_1_126 75 107 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 107 186 (Polychromatic418967fa.accept_9_2_8_6_1_79 74 107 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 107 186 (accept_3_4 73 107 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 107 186 (Polychromatic418967fa.accept_13_7_3_4_1_459 72 107 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 107 186
  (Polychromatic418967fa.accept_10_1_7_6_1_91 71 107 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 107 186 (accept_3_4 70 107 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 107 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 107 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 107 186 (Polychromatic418967fa.accept_7_5_2_4_1_126 68 107 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 107 186 (accept_3_4 67 107 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 107 186 (Polychromatic418967fa.accept_9_3_8_6_1_80 66 107 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 107 186
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 107 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 107 186 (accept_3_4 64 107 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 107 186 (Polychromatic418967fa.accept_10_3_7_6_1_659 63 107 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 107 186 (Polychromatic418967fa.accept_7_6_2_4_1_291 62 107 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 107 186 (accept_3_4 61 107 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 107 186 (Polychromatic418967fa.accept_16_12_11_10_1_1667 60 107 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 107 186
  (Polychromatic418967fa.accept_9_5_8_6_1_281 59 107 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 107 186 (accept_3_4 58 107 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 107 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 107 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 107 186 (Polychromatic418967fa.accept_9_2_8_6_1_79 56 107 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 107 186 (accept_3_4 55 107 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 107 186 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 107 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 107 186
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 107 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 107 186 (accept_3_4 52 107 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 107 186 (Polychromatic418967fa.accept_10_1_7_6_1_91 51 107 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 107 186 (Polychromatic418967fa.accept_9_5_8_6_1_281 50 107 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 107 186 (accept_3_4 49 107 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 107 186 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 107 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 107 186
  (Polychromatic418967fa.accept_7_5_2_4_1_126 47 107 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 107 186 (accept_3_4 46 107 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 107 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 107 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 107 186 (Polychromatic418967fa.accept_14_2_9_4_1_1735 44 107 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 107 186 (accept_3_4 43 107 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 107 186 (Polychromatic418967fa.accept_11_9_8_10_1_934 42 107
  186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 107 186
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 107 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 107 186 (accept_3_4 40 107 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 107 186 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 107 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 107 186 (Polychromatic418967fa.accept_9_2_8_6_1_79 38 107 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 107 186 (accept_3_4 37 107 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 107 186 (Polychromatic418967fa.accept_17_2_5_16_1_1264 36 107 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 107 186
  (Polychromatic418967fa.accept_17_1_5_16_1_5589 35 107 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 107 186 (accept_3_4 34 107 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 107 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 107 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 107 186 (Polychromatic418967fa.accept_9_5_8_6_1_281 32 107 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 107 186 (accept_3_4 31 107 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 107 186 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 107 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 107 186
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 107 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 107 186 (accept_3_4 28 107 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 107 186 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 107 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 107 186 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 107 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 107 186 (accept_3_4 25 107 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 107 186 (Polychromatic418967fa.accept_19_5_12_15_1_9244 24 107 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 107 186
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 107 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 107 186 (accept_3_4 22 107 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 107 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 107 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 107 186 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 107 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 107 186 (accept_3_4 19 107 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 107 186 (Polychromatic418967fa.accept_17_1_5_16_1_5589 18 107 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 107 186
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 107 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 107 186 (accept_3_4 16 107 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 107 186 (Polychromatic418967fa.accept_16_15_11_10_1_3639 15 107 186 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 186 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 107 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 107 186 (accept_3_4 13 107 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 107 186 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 107 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 107 186
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 107 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 107 186 (accept_3_4 10 107 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  107 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 107 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 107 186 (Polychromatic418967fa.accept_15_8_2_6_1_2125 8 107 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 107 186 (accept_3_4 7 107 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 107 186 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 107 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 107 186
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 107 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 107 186 (accept_3_4 4 107 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  107 186 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 107 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 107 186 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 107 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 107 186 (accept_3_4 1 107 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 107 186))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 81 106 186 (Eq.refl Bool.true) (allA_succ_of_gcd 80 106 186 2 40 53 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 106 186
  (Polychromatic418967fa.accept_24_7_10_18_1_10688 79 106 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 106 186 2 39 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 106 186 (accept_3_5 77 106 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 106 186 2 38 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 106 186 (Polychromatic418967fa.accept_7_5_1_4_1_122 75 106 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 106 186 2 37 53 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 106 186
  (Polychromatic418967fa.accept_7_3_1_4_1_121 73 106 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 106 186 2 36 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 106 186 (accept_3_5 71 106 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 106 186 2 35 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 106 186 (Polychromatic418967fa.accept_11_3_7_10_1_180 69 106 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 106 186 2 34 53 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 106 186
  (Polychromatic418967fa.accept_9_4_7_6_1_255 67 106 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 106 186 2 33 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 106 186 (accept_3_5 65 106 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 106 186 2 32 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 106 186 (Polychromatic418967fa.accept_12_3_10_6_1_442 63 106 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 106 186 2 31 53 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 106 186
  (Polychromatic418967fa.accept_7_5_1_4_1_122 61 106 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 106 186 2 30 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 106 186 (accept_3_5 59 106 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 106 186 2 29 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 106 186 (Polychromatic418967fa.accept_9_3_7_6_1_76 57 106 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 106 186 2 28 53 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 106 186
  (Polychromatic418967fa.accept_9_1_7_6_1_75 55 106 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 106 186 2 27 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 106 186 (accept_3_5 53 106 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 106 186 2 26 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 106 186 (Polychromatic418967fa.accept_12_3_10_6_1_442 51 106 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 106 186 2 25 53 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 106 186
  (Polychromatic418967fa.accept_9_4_7_6_1_255 49 106 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 106 186 2 24 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 106 186 (accept_3_5 47 106 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 106 186 2 23 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 106 186 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 106 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 106 186 2 22 53 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 106 186
  (Polychromatic418967fa.accept_19_5_11_15_1_2460 43 106 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 106 186 2 21 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 106 186 (accept_3_5 41 106 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 106 186 2 20 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 106 186 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 106 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 106 186 2 19 53 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 106 186
  (Polychromatic418967fa.accept_9_1_7_6_1_75 37 106 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 106 186 2 18 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 106 186 (accept_3_5 35 106 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 106 186 2 17 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 106 186 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 106 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 106 186 2 16 53 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 106 186
  (Polychromatic418967fa.accept_7_3_1_4_1_121 31 106 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 106 186 2 15 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 106 186 (accept_3_5 29 106 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 106 186 2 14 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 106 186 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 106 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 106 186 2 13 53 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 106 186
  (Polychromatic418967fa.accept_11_3_7_10_1_180 25 106 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 106 186 2 12 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 106 186 (accept_3_5 23 106 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 106 186 2 11 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 106 186 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 106 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 106 186 2 10 53 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 106 186
  (Polychromatic418967fa.accept_7_5_1_4_1_122 19 106 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 106 186 2 9 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 106 186 (accept_3_5 17 106 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  106 186 2 8 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 106 186 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 106 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 106 186 2 7 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 106 186 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 106 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 106 186 2 6 53 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 106 186 (accept_3_5 11 106 186
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 106 186 2 5 53 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 106 186
  (Polychromatic418967fa.accept_12_9_10_6_1_872 9 106 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 106 186 2 4 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 106 186 (Polychromatic418967fa.accept_15_7_1_6_1_6150 7 106 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 106 186 2 3 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 106 186 (accept_3_5 5 106 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 106 186 2 2 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 106 186 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 106 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 106 186 2 1 53 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 106 186 (Polychromatic418967fa.accept_9_1_7_6_1_75 1
  106 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106
  186))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 82 105 186 (Eq.refl
  Bool.true) (allA_succ_of_gcd 81 105 186 3 27 35 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 80 105 186 (Polychromatic418967fa.accept_12_8_9_6_1_127 80 105 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 105 186
  (Polychromatic418967fa.accept_4_3_1_2_1_62 79 105 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 105 186 3 26 35 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 105 186 (Polychromatic418967fa.accept_18_5_15_6_1_3999 77 105 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 105 186
  (Polychromatic418967fa.accept_12_4_9_6_1_440 76 105 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 105 186 3 25 35 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 105 186 (Polychromatic418967fa.accept_10_4_5_6_1_651 74 105 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 105 186 (Polychromatic418967fa.accept_14_3_7_4_1_118
  73 105 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 105 186 3 24 35 62
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 105 186
  (Polychromatic418967fa.accept_4_3_1_2_1_62 71 105 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 105 186 (Polychromatic418967fa.accept_12_10_9_6_1_1445 70 105 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 105 186 3 23 35 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 105 186 (Polychromatic418967fa.accept_12_8_9_6_1_127
  68 105 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 105 186
  (Polychromatic418967fa.accept_4_3_1_2_1_62 67 105 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 105 186 3 22 35 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 105 186 (Polychromatic418967fa.accept_16_1_9_10_1_4740 65 105 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 105 186
  (Polychromatic418967fa.accept_10_4_5_6_1_651 64 105 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 105 186 3 21 35 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 105 186 (Polychromatic418967fa.accept_12_2_9_6_1_439 62 105 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 186 (Polychromatic418967fa.accept_10_1_5_6_1_649
  61 105 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 105 186 3 20 35 62
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 105 186
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 105 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 105 186 (Polychromatic418967fa.accept_12_10_9_6_1_1445 58 105 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 105 186 3 19 35 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 105 186 (Polychromatic418967fa.accept_12_8_9_6_1_127
  56 105 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 105 186
  (Polychromatic418967fa.accept_4_3_1_2_1_62 55 105 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 105 186 3 18 35 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 105 186 (Polychromatic418967fa.accept_14_11_7_4_1_3449 53 105 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 105 186
  (Polychromatic418967fa.accept_12_4_9_6_1_440 52 105 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 105 186 3 17 35 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 105 186 (Polychromatic418967fa.accept_12_2_9_6_1_439 50 105 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 105 186 (Polychromatic418967fa.accept_10_9_5_6_1_691
  49 105 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 105 186 3 16 35 62
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 105 186
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 105 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 105 186 (Polychromatic418967fa.accept_12_10_9_6_1_1445 46 105 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 105 186 3 15 35 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 105 186 (Polychromatic418967fa.accept_10_4_5_6_1_651
  44 105 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 186
  (Polychromatic418967fa.accept_4_3_1_2_1_62 43 105 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 105 186 3 14 35 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 105 186 (Polychromatic418967fa.accept_10_1_5_6_1_649 41 105 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 105 186 (Polychromatic418967fa.accept_12_4_9_6_1_440
  40 105 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 105 186 3 13 35 62
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 105 186
  (Polychromatic418967fa.accept_11_5_6_10_1_1432 38 105 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 105 186 (Polychromatic418967fa.accept_22_15_17_10_1_10687 37 105 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 105 186 3 12 35 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 105 186
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 105 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 105 186 (Polychromatic418967fa.accept_10_4_5_6_1_651 34 105 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 105 186 3 11 35 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 105 186 (Polychromatic418967fa.accept_12_8_9_6_1_127
  32 105 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 186
  (Polychromatic418967fa.accept_4_3_1_2_1_62 31 105 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 105 186 3 10 35 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 105 186 (Polychromatic418967fa.accept_10_9_5_6_1_691 29 105 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 186 (Polychromatic418967fa.accept_12_4_9_6_1_440
  28 105 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 105 186 3 9 35 62
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 105 186
  (Polychromatic418967fa.accept_12_2_9_6_1_439 26 105 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 105 186 (Polychromatic418967fa.accept_14_11_7_4_1_3449 25 105 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 105 186 3 8 35 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 105 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 23
  105 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 186
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 105 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 105 186 3 7 35 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 105 186 (Polychromatic418967fa.accept_12_8_9_6_1_127 20 105 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 105 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 105 186 3 6 35 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 105 186
  (Polychromatic418967fa.accept_14_3_7_4_1_118 17 105 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 105 186 (Polychromatic418967fa.accept_11_5_6_10_1_1432 16 105 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 105 186 3 5 35 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 105 186 (Polychromatic418967fa.accept_10_4_5_6_1_651
  14 105 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 186
  (Polychromatic418967fa.accept_17_13_3_16_1_5599 13 105 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 105 186 3 4 35 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 105 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 105 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 105 186
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 105 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 105 186 3 3 35 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 105 186 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 105 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 186 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 105 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 105 186 3 2 35 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 105 186
  (Polychromatic418967fa.accept_11_5_6_10_1_1432 5 105 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 105 186 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 105 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 105 186 3 1 35 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 105 186 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 105 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 186
  (Polychromatic418967fa.accept_10_1_5_6_1_649 1 105 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 105 186)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 104
  186 (Eq.refl Bool.true) (allA_succ_of_gcd 82 104 186 2 41 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 104 186 (Polychromatic418967fa.accept_11_4_5_10_1_926 81 104
  186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 104 186 2 40 52 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 104 186 (accept_3_4 79
  104 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 104 186 2 39 52 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 104 186
  (Polychromatic418967fa.accept_21_14_20_18_1_9174 77 104 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 76 104 186 2 38 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 75 104 186 (Polychromatic418967fa.accept_7_5_6_4_1_117 75 104 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 104 186 2 37 52 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 104 186 (accept_3_4 73 104 186
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 104 186 2 36 52 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 104 186
  (Polychromatic418967fa.accept_9_8_5_6_1_538 71 104 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 104 186 2 35 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 104 186 (Polychromatic418967fa.accept_12_9_8_6_1_466 69 104 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 104 186 2 34 52 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 104 186 (accept_3_4 67 104 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 104 186 2 33 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 104 186 (Polychromatic418967fa.accept_7_2_6_4_1_29 65
  104 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 104 186 2 32 52 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 104 186
  (Polychromatic418967fa.accept_12_3_8_6_1_895 63 104 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 104 186 2 31 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 104 186 (accept_3_4 61 104 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 104 186 2 30 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 104 186 (Polychromatic418967fa.accept_7_3_6_4_1_30 59 104 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 104 186 2 29 52 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 104 186
  (Polychromatic418967fa.accept_9_3_5_6_1_253 57 104 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 104 186 2 28 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 104 186 (accept_3_4 55 104 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 104 186 2 27 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 104 186 (Polychromatic418967fa.accept_9_8_5_6_1_538 53 104 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 104 186 2 26 52 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 104 186
  (Polychromatic418967fa.accept_7_2_6_4_1_29 51 104 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 104 186 2 25 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 104 186 (accept_3_4 49 104 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 104 186 2 24 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 104 186 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 104 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 104 186 2 23 52 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 104 186
  (Polychromatic418967fa.accept_7_3_6_4_1_30 45 104 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 104 186 2 22 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 104 186 (accept_3_4 43 104 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 104 186 2 21 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 104 186 (Polychromatic418967fa.accept_19_3_9_15_1_9240 41 104 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 104 186 2 20 52 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 104 186
  (Polychromatic418967fa.accept_9_3_5_6_1_253 39 104 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 104 186 2 19 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 104 186 (accept_3_4 37 104 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 104 186 2 18 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 104 186 (Polychromatic418967fa.accept_9_8_5_6_1_538 35 104 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 104 186 2 17 52 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 104 186
  (Polychromatic418967fa.accept_7_5_6_4_1_117 33 104 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 104 186 2 16 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 104 186 (accept_3_4 31 104 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 104 186 2 15 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 104 186 (Polychromatic418967fa.accept_9_2_5_6_1_536 29 104 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 104 186 2 14 52 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 104 186
  (Polychromatic418967fa.accept_12_3_8_6_1_895 27 104 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 104 186 2 13 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 104 186 (accept_3_4 25 104 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 104 186 2 12 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 104 186 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 104 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 104 186 2 11 52 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 104 186
  (Polychromatic418967fa.accept_9_3_5_6_1_253 21 104 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 104 186 2 10 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 104 186 (accept_3_4 19 104 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 104 186 2 9 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 104 186 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 104 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 104 186 2 8 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 104 186 (Polychromatic418967fa.accept_10_5_4_6_1_319
  15 104 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 104 186 2 7 52 93
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 104 186
  (accept_3_4 13 104 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 104 186 2 6 52 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 104 186
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 104 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 104 186 2 5 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 104 186 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 104 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 104 186 2 4 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 104 186 (accept_3_4 7 104 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 104 186 2 3 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 104 186 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 104 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 104 186 2 2 52 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 104 186 (Polychromatic418967fa.accept_7_3_6_4_1_30 3
  104 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 104 186 2 1 52 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 104 186 (accept_3_4 1
  104 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  186))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 84 103 186 (Eq.refl
  Bool.true) (allA_succ_of_accept 83 103 186 (accept_3_5 83 103 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 103 186 (Polychromatic418967fa.accept_9_1_4_6_1_5 82 103 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 103 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 103 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 103 186 (accept_3_5 80 103 186
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 103 186 (Polychromatic418967fa.accept_7_2_5_4_1_115
  79 103 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 103 186
  (Polychromatic418967fa.accept_7_1_5_4_1_134 78 103 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 103 186 (accept_3_5 77 103 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 103 186 (Polychromatic418967fa.accept_7_6_5_4_1_297 76 103 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 103 186 (Polychromatic418967fa.accept_9_3_4_6_1_252 75 103 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 103 186 (accept_3_5 74 103 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 103 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 103 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 103 186
  (Polychromatic418967fa.accept_7_2_5_4_1_115 72 103 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 103 186 (accept_3_5 71 103 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 103 186 (Polychromatic418967fa.accept_9_7_4_6_1_273 70 103 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 103 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 103 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 103 186 (accept_3_5 68 103 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 103 186 (Polychromatic418967fa.accept_10_7_3_6_1_644 67 103 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 103 186
  (Polychromatic418967fa.accept_9_3_4_6_1_252 66 103 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 103 186 (accept_3_5 65 103 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 103 186 (Polychromatic418967fa.accept_7_1_5_4_1_134 64 103 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 103 186 (Polychromatic418967fa.accept_13_11_12_4_1_3945 63 103 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 103 186 (accept_3_5 62 103 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 103 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 103 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 103 186
  (Polychromatic418967fa.accept_11_5_4_10_1_524 60 103 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 103 186 (accept_3_5 59 103 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 103 186 (Polychromatic418967fa.accept_7_2_5_4_1_115 58 103 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 103 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 103 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 103 186 (accept_3_5 56 103 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 103 186 (Polychromatic418967fa.accept_7_6_5_4_1_297 55 103 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 103 186
  (Polychromatic418967fa.accept_13_2_12_4_1_943 54 103 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 103 186 (accept_3_5 53 103 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 103 186 (Polychromatic418967fa.accept_9_7_4_6_1_273 52 103 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 103 186 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 103 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 103 186 (accept_3_5 50 103 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 103 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 103 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 103 186
  (Polychromatic418967fa.accept_7_6_5_4_1_297 48 103 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 103 186 (accept_3_5 47 103 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 103 186 (Polychromatic418967fa.accept_9_1_4_6_1_5 46 103 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 103 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 103 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 103 186 (accept_3_5 44 103 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 103 186 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 103 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 103 186
  (Polychromatic418967fa.accept_13_3_12_4_1_110 42 103 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 103 186 (accept_3_5 41 103 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 103 186 (Polychromatic418967fa.accept_19_2_8_15_1_2447 40 103 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 103 186 (Polychromatic418967fa.accept_9_3_4_6_1_252 39 103 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 103 186 (accept_3_5 38 103 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 103 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 103 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 103 186
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 103 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 103 186 (accept_3_5 35 103 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 103 186 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 103 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 103 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 103 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 103 186 (accept_3_5 32 103 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 103 186 (Polychromatic418967fa.accept_13_5_12_4_1_449 31 103 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 103 186
  (Polychromatic418967fa.accept_7_2_5_4_1_115 30 103 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 103 186 (accept_3_5 29 103 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 103 186 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 103 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 103 186 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 103 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 103 186 (accept_3_5 26 103 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 103 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 103 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 103 186
  (Polychromatic418967fa.accept_13_11_12_4_1_3945 24 103 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 103 186 (accept_3_5 23 103 186 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 103 186 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 103 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 103 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 103 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 103 186 (accept_3_5 20 103 186
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 103 186 (Polychromatic418967fa.accept_9_1_4_6_1_5 19
  103 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 103 186
  (Polychromatic418967fa.accept_10_8_3_6_1_685 18 103 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 103 186 (accept_3_5 17 103 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 103 186 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 103 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 103 186 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 103 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 103 186 (accept_3_5 14 103 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 103 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 103 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 103 186
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 103 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 103 186 (accept_3_5 11 103 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 103 186 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 103 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 103 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 103 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 103 186 (accept_3_5 8 103 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 103 186 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 103 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 103 186
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 103 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 103 186 (accept_3_5 5 103 186 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  103 186 (Polychromatic418967fa.accept_15_4_13_6_1_642 4 103 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 103 186 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 103 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 103 186 (accept_3_5 2 103 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 103 186 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 103 186 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 103
  186)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 85 102 186
  (Eq.refl Bool.true) (allA_succ_of_gcd 84 102 186 6 14 17 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 102 186 (Polychromatic418967fa.accept_9_2_3_6_1_88 83 102 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 102 186 2 41 51 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 102 186 3 27 34 62
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 102 186 2 40 51
  93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 102 186
  (Polychromatic418967fa.accept_9_7_3_6_1_270 79 102 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 102 186 6 13 17 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 102 186 (Polychromatic418967fa.accept_9_5_3_6_1_269 77 102 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 102 186 2 38 51 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 102 186 3 25 34 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 102 186 2 37 51 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 102 186
  (Polychromatic418967fa.accept_9_1_3_6_1_70 73 102 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 102 186 6 12 17 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 102 186 (Polychromatic418967fa.accept_9_8_3_6_1_533 71 102 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 102 186 2 35 51 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 102 186 3 23 34 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 102 186 2 34 51 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 102 186
  (Polychromatic418967fa.accept_9_4_3_6_1_532 67 102 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 102 186 6 11 17 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 102 186 (Polychromatic418967fa.accept_9_2_3_6_1_88 65 102 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 102 186 2 32 51 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 102 186 3 21 34 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 102 186 2 31 51 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 102 186
  (Polychromatic418967fa.accept_9_7_3_6_1_270 61 102 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 102 186 6 10 17 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 102 186 (Polychromatic418967fa.accept_9_5_3_6_1_269 59 102 186 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 102 186 2 29 51 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 102 186 3 19 34 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 102 186 2 28 51 93 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 102 186
  (Polychromatic418967fa.accept_9_1_3_6_1_70 55 102 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 102 186 6 9 17 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 102 186 (Polychromatic418967fa.accept_9_8_3_6_1_533 53 102 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 102 186 2 26 51 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 102 186 3 17 34 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 102 186 2 25 51 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 102 186
  (Polychromatic418967fa.accept_9_4_3_6_1_532 49 102 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 102 186 6 8 17 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 102 186 (Polychromatic418967fa.accept_9_2_3_6_1_88 47 102 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 102 186 2 23 51 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 102 186 3 15 34 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 102 186 2 22 51 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 102 186
  (Polychromatic418967fa.accept_9_7_3_6_1_270 43 102 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 102 186 6 7 17 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 102 186 (Polychromatic418967fa.accept_9_5_3_6_1_269 41 102 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 102 186 2 20 51 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 102 186 3 13 34 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 102 186 2 19 51 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 102 186
  (Polychromatic418967fa.accept_9_1_3_6_1_70 37 102 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 186 6 6 17 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 102 186 (Polychromatic418967fa.accept_9_8_3_6_1_533 35 102 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 102 186 2 17 51 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 102 186 3 11 34 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 102 186 2 16 51 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 102 186
  (Polychromatic418967fa.accept_9_4_3_6_1_532 31 102 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 186 6 5 17 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 102 186 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 102 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 102 186 2 14 51 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 102 186 3 9 34 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 102 186 2 13 51 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 102 186
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 102 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 186 6 4 17 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 102 186 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 102 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 102 186 2 11 51 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 102 186 3 7 34 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 102 186 2 10 51 93 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 102 186
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 102 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 186 6 3 17 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 102 186 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 102 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 102 186 2 8 51 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 102 186 3 5 34 62 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 102 186 2 7 51 93 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 102 186 (Polychromatic418967fa.accept_9_4_3_6_1_532 13
  102 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 102 186 6 2 17 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 102 186
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 102 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 102 186 2 5 51 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 102 186 3 3 34 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 102 186 2 4 51 93 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 102 186 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 102 186 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102 186 6 1 17 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 102 186 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 102 186
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 102 186 2 2 51 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 102 186 3 1 34 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 102 186 2 1 51 93 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 186
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 102 186 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 102 186)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_186_segment_000))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


