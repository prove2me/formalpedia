-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch177
-- name    : Polychromatic418967fa_Branch177
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:18:54.430377+00:00
-- url     : https://prove2.me/theorems/b7e95ef4-4692-4dfc-b5c4-9a3b306d754e
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch177_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_177 : allB 177 177 :=
  allB_succ' 2 176 177 (Eq.refl Bool.true) (allA_succ_of_accept 1 176 177 (accept_3_4 1 176 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 176 177)) (allB_succ' 3 175 177 (Eq.refl Bool.true) (allA_succ_of_accept 2 175 177
  (accept_3_5 2 175 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 175 177
  (Polychromatic418967fa.accept_9_1_4_6_1_5 1 175 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 175 177))) (allB_succ' 4 174 177 (Eq.refl Bool.true) (allA_succ_of_gcd 3 174 177 3 1 58 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 174 177
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 174 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 174 177 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 174 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 174 177)))) (allB_succ' 5 173 177 (Eq.refl Bool.true) (allA_succ_of_accept 4
  173 177 (accept_3_4 4 173 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 173 177
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 173 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 173 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 173 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 173 177 (accept_3_4 1 173 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 173 177))))) (allB_succ' 6 172 177 (Eq.refl Bool.true) (allA_succ_of_accept 5 172 177
  (accept_3_5 5 172 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 172 177
  (Polychromatic418967fa.accept_9_4_1_6_1_284 4 172 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 172 177 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 172 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 172 177 (accept_3_5 2 172 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 172 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 172 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 172 177)))))) (allB_succ' 7 171 177 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 171 177 3 2 57 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 171 177 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 171 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 171 177 (Polychromatic418967fa.accept_10_4_1_7_1_371 4 171 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 171 177 3 1 57 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 171 177
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 171 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 171 177 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 171 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 171 177))))))) (allB_succ' 8 170 177 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 170 177 (accept_3_4 7 170 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  170 177 (Polychromatic418967fa.accept_11_6_5_1_1_586 6 170 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 170 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 170 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 170 177 (accept_3_4 4 170 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 170 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 170 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 170 177
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 170 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 170 177 (accept_3_4 1 170 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 170
  177)))))))) (allB_succ' 9 169 177 (Eq.refl Bool.true) (allA_succ_of_accept 8 169 177 (accept_3_5 8 169 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 169 177 (Polychromatic418967fa.accept_15_7_4_12_1_2530 7 169
  177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 169 177
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 169 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 169 177 (accept_3_5 5 169 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  169 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 169 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 169 177 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 169 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 169 177 (accept_3_5 2 169 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 169 177 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 169 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 169 177))))))))) (allB_succ' 10 168 177 (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 168 177 3 3 56 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 168 177 (Polychromatic418967fa.accept_15_8_3_12_1_1657 8 168 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 168 177 (Polychromatic418967fa.accept_13_7_12_8_1_199
  7 168 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 168 177 3 2 56 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 168 177
  (Polychromatic418967fa.accept_10_5_8_7_1_2174 5 168 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 168 177 (Polychromatic418967fa.accept_13_4_12_8_1_197 4 168 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 168 177 3 1 56 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 168 177 (Polychromatic418967fa.accept_11_2_3_1_1_244 2 168 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 168 177
  (Polychromatic418967fa.accept_13_1_12_8_1_1818 1 168 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 168 177)))))))))) (allB_succ' 11 167 177 (Eq.refl Bool.true) (allA_succ_of_accept 10 167 177 (accept_3_4 10
  167 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 167 177
  (Polychromatic418967fa.accept_13_9_11_8_1_195 9 167 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 167 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 167 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 167 177 (accept_3_4 7 167 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 167 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 167 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 167 177 (Polychromatic418967fa.accept_15_5_2_12_1_2543
  5 167 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 167 177 (accept_3_4 4
  167 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 167 177
  (Polychromatic418967fa.accept_7_3_6_2_1_90 3 167 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 167 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 167 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 167 177 (accept_3_4 1 167 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 167 177))))))))))) (allB_succ' 12 166 177 (Eq.refl Bool.true) (allA_succ_of_accept 11 166 177
  (accept_3_5 11 166 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 166 177
  (Polychromatic418967fa.accept_7_3_5_2_1_17 10 166 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 166 177 (Polychromatic418967fa.accept_18_9_4_15_1_555 9 166 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 166 177 (accept_3_5 8 166 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 166 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 166 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 166 177 (Polychromatic418967fa.accept_12_6_10_9_1_531
  6 166 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 166 177 (accept_3_5 5
  166 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 166 177
  (Polychromatic418967fa.accept_7_4_5_2_1_243 4 166 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 166 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 166 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 166 177 (accept_3_5 2 166 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 166 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 166 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 166 177)))))))))))) (allB_succ' 13 165 177 (Eq.refl Bool.true)
  (allA_succ_of_gcd 12 165 177 3 4 55 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 165 177 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 165 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 165 177 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 165 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 165 177 3 3 55 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 165 177
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 165 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 165 177 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 165 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 165 177 3 2 55 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 165 177 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 165 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 165 177
  (Polychromatic418967fa.accept_8_4_5_1_1_299 4 165 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 165 177 3 1 55 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 165 177 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 165 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 177 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 165 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 165 177))))))))))))) (allB_succ' 14 164 177
  (Eq.refl Bool.true) (allA_succ_of_accept 13 164 177 (accept_3_4 13 164 177 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 164 177 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 164 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 164 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 164 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 164 177 (accept_3_4 10 164 177
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 164 177 (Polychromatic418967fa.accept_11_9_10_1_1_581
  9 164 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 164 177
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 164 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 164 177 (accept_3_4 7 164 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  164 177 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 164 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 164 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 164 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 164 177 (accept_3_4 4 164 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 164 177 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 164 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 164 177
  (Polychromatic418967fa.accept_10_2_4_7_1_352 2 164 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 164 177 (accept_3_4 1 164 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 164
  177)))))))))))))) (allB_succ' 15 163 177 (Eq.refl Bool.true) (allA_succ_of_accept 14 163 177 (accept_3_5 14 163 177
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 163 177 (Polychromatic418967fa.accept_9_4_1_6_1_284
  13 163 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 163 177
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 163 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 163 177 (accept_3_5 11 163 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 163 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 163 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 163 177 (Polychromatic418967fa.accept_13_9_7_8_1_1122 9 163 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 163 177 (accept_3_5 8 163 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 163 177 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 163 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 163 177
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 163 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 163 177 (accept_3_5 5 163 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  163 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 163 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 163 177 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 163 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 163 177 (accept_3_5 2 163 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 163 177 (Polychromatic418967fa.accept_13_1_7_8_1_1796 1 163 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 163 177))))))))))))))) (allB_succ' 16 162 177 (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 162 177 3 5 54 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 162 177 (Polychromatic418967fa.accept_10_4_2_7_1_373 14 162 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 162 177 (Polychromatic418967fa.accept_7_6_1_2_1_230
  13 162 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 162 177 3 4 54 59
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 162 177
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 162 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 162 177 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 162 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 162 177 3 3 54 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 162 177 (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 162 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 162 177
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 162 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 162 177 3 2 54 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 162 177 (Polychromatic418967fa.accept_10_5_2_7_1_345 5 162 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 162 177 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 162 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 162 177 3 1 54 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 162 177
  (Polychromatic418967fa.accept_12_2_6_9_1_19 2 162 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 162 177 (Polychromatic418967fa.accept_13_1_6_8_1_208 1 162 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 162 177)))))))))))))))) (allB_succ' 17 161 177 (Eq.refl Bool.true)
  (allA_succ_of_accept 16 161 177 (accept_3_4 16 161 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 161 177 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 161 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 161 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 161 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 161 177 (accept_3_4 13 161 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 161 177 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 161 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 161 177
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 161 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 161 177 (accept_3_4 10 161 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  161 177 (Polychromatic418967fa.accept_18_9_17_15_1_2267 9 161 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 161 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 161 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 161 177 (accept_3_4 7 161 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 161 177 (Polychromatic418967fa.accept_10_6_1_7_1_342 6 161 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 161 177
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 161 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 161 177 (accept_3_4 4 161 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  161 177 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 161 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 161 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 161 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 161 177 (accept_3_4 1 161 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 161 177))))))))))))))))) (allB_succ' 18 160 177 (Eq.refl Bool.true)
  (allA_succ_of_accept 17 160 177 (accept_3_5 17 160 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 160 177 (Polychromatic418967fa.accept_11_5_6_1_1_988 16 160 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 160 177 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 160 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 160 177 (accept_3_5 14 160 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 160 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 160 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 160 177
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 160 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 160 177 (accept_3_5 11 160 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 160 177 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 160 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 160 177 (Polychromatic418967fa.accept_13_9_4_8_1_1752 9 160 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 160 177 (accept_3_5 8 160 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 160 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 160 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 160 177
  (Polychromatic418967fa.accept_12_6_4_9_1_544 6 160 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 160 177 (accept_3_5 5 160 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  160 177 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 160 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 160 177 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 160 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 160 177 (accept_3_5 2 160 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 160 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 160 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 160 177)))))))))))))))))) (allB_succ' 19 159 177
  (Eq.refl Bool.true) (allA_succ_of_gcd 18 159 177 3 6 53 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 159 177 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 159 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 159 177
  (Polychromatic418967fa.accept_17_16_6_7_1_2715 16 159 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 159 177 3 5 53 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 159 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 159 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 177 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 159
  177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 159 177 3 4 53 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 159 177
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 159 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 159 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 159 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 159 177 3 3 53 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 159 177 (Polychromatic418967fa.accept_10_8_9_7_1_1118 8 159 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 177
  (Polychromatic418967fa.accept_12_7_3_9_1_999 7 159 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 159 177 3 2 53 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 159 177 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 159 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 159 177 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 159 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 159 177 3 1 53 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 159 177
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 159 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 159 177 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 159 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 159 177))))))))))))))))))) (allB_succ' 20 158 177 (Eq.refl Bool.true)
  (allA_succ_of_accept 19 158 177 (accept_3_4 19 158 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 158 177 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 158 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 158 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 158 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 158 177 (accept_3_4 16 158 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 158 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 158 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 158 177
  (Polychromatic418967fa.accept_27_14_23_15_1_10000 14 158 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 158 177 (accept_3_4 13 158 177 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 158 177 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 158 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 158 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 158 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 158 177 (accept_3_4 10 158 177
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 158 177 (Polychromatic418967fa.accept_10_9_8_7_1_714 9
  158 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 158 177
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 158 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 158 177 (accept_3_4 7 158 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  158 177 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 158 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 158 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 158 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 158 177 (accept_3_4 4 158 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 158 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 158 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 158 177
  (Polychromatic418967fa.accept_9_2_5_6_1_536 2 158 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 158 177 (accept_3_4 1 158 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158
  177)))))))))))))))))))) (allB_succ' 21 157 177 (Eq.refl Bool.true) (allA_succ_of_accept 20 157 177 (accept_3_5 20 157
  177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 157 177
  (Polychromatic418967fa.accept_7_5_3_2_1_249 19 157 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 157 177 (Polychromatic418967fa.accept_13_5_1_8_1_1115 18 157 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 157 177 (accept_3_5 17 157 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 157 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 157 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 157 177 (Polychromatic418967fa.accept_7_1_3_2_1_13 15
  157 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 157 177 (accept_3_5 14
  157 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 157 177
  (Polychromatic418967fa.accept_7_6_3_2_1_461 13 157 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 157 177 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 157 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 157 177 (accept_3_5 11 157 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 157 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 157 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 157 177 (Polychromatic418967fa.accept_13_9_1_8_1_1742
  9 157 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 157 177 (accept_3_5 8
  157 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 157 177
  (Polychromatic418967fa.accept_9_7_4_6_1_273 7 157 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 157 177 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 157 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 157 177 (accept_3_5 5 157 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 157 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 157 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 157 177 (Polychromatic418967fa.accept_9_3_4_6_1_252 3
  157 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 157 177 (accept_3_5 2 157
  177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 157 177 (Polychromatic418967fa.accept_7_1_3_2_1_13
  1 157 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 157 177)))))))))))))))))))))
  (allB_succ' 22 156 177 (Eq.refl Bool.true) (allA_succ_of_gcd 21 156 177 3 7 52 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 156 177
  (Polychromatic418967fa.accept_9_2_3_6_1_88 20 156 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 156 177 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 156 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 156 177 3 6 52 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 156 177 (Polychromatic418967fa.accept_9_8_3_6_1_533 17
  156 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 156 177
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 156 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 156 177 3 5 52 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 156 177 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 156 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 156 177 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 156 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 156 177 3 4 52 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 156 177
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 156 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 156 177 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 156 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 156 177 3 3 52 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 156 177 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 156 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 156 177
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 156 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 156 177 3 2 52 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 156 177 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 156 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 156 177 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 156 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 156 177 3 1 52 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 156 177
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 156 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 156 177 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 156 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 156 177)))))))))))))))))))))) (allB_succ' 23 155 177 (Eq.refl Bool.true)
  (allA_succ_of_accept 22 155 177 (accept_3_4 22 155 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 155 177 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 155 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 155 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 155 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 155 177 (accept_3_4 19 155 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 155 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 155 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 155 177
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 155 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 155 177 (accept_3_4 16 155 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 155 177 (Polychromatic418967fa.accept_12_3_11_9_1_193 15 155 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 155 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 155 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 155 177 (accept_3_4 13 155 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 155 177 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 155 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 155 177
  (Polychromatic418967fa.accept_33_11_23_12_1_9999 11 155 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 155 177 (accept_3_4 10 155 177 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 155 177 (Polychromatic418967fa.accept_13_9_12_8_1_570 9 155 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 155 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 155 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 155 177 (accept_3_4 7 155 177
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 155 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 6
  155 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 155 177
  (Polychromatic418967fa.accept_9_5_2_6_1_265 5 155 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 155 177 (accept_3_4 4 155 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  155 177 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 155 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 155 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 155 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 155 177 (accept_3_4 1 155 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 155 177))))))))))))))))))))))) (allB_succ' 24 154 177 (Eq.refl Bool.true)
  (allA_succ_of_accept 23 154 177 (accept_3_5 23 154 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 154 177 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 154 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 154 177 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 154 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 154 177 (accept_3_5 20 154 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 154 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 154 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 154 177
  (Polychromatic418967fa.accept_12_6_10_9_1_531 18 154 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 154 177 (accept_3_5 17 154 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 154 177 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 154 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 154 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 154 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 154 177 (accept_3_5 14 154 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 154 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 154 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 154 177
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 154 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 154 177 (accept_3_5 11 154 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 154 177 (Polychromatic418967fa.accept_13_10_11_8_1_1770 10 154 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 154 177 (Polychromatic418967fa.accept_13_9_11_8_1_195 9 154 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 154 177 (accept_3_5 8 154 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 154 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 154 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 154 177
  (Polychromatic418967fa.accept_12_6_10_9_1_531 6 154 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 154 177 (accept_3_5 5 154 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  154 177 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 154 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 154 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 154 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 154 177 (accept_3_5 2 154 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 154 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 154 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 154 177)))))))))))))))))))))))) (allB_succ' 25 153 177
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 153 177 3 8 51 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 153 177 (Polychromatic418967fa.accept_15_8_3_12_1_1657 23 153 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 153 177
  (Polychromatic418967fa.accept_7_1_6_2_1_18 22 153 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 153 177 3 7 51 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 153 177 (Polychromatic418967fa.accept_11_9_10_1_1_581 20 153 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 177 (Polychromatic418967fa.accept_23_19_15_16_1_9998 19
  153 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 153 177 3 6 51 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 153 177
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 153 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 153 177 (Polychromatic418967fa.accept_10_6_3_7_1_2197 16 153 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 153 177 3 5 51 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 153 177 (Polychromatic418967fa.accept_10_4_3_7_1_1110
  14 153 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 177
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 13 153 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 153 177 3 4 51 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 153 177 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 153 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 153 177 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 153 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 153 177 3 3 51 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 153 177
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 153 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 153 177 (Polychromatic418967fa.accept_13_7_10_8_1_567 7 153 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 153 177 3 2 51 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 153 177 (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 153 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 177
  (Polychromatic418967fa.accept_7_4_6_2_1_451 4 153 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 153 177 3 1 51 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 153 177 (Polychromatic418967fa.accept_11_2_10_1_1_1017 2 153 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 177 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 153 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 153 177))))))))))))))))))))))))) (allB_succ' 26
  152 177 (Eq.refl Bool.true) (allA_succ_of_accept 25 152 177 (accept_3_4 25 152 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 152 177 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 152 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 152 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 23
  152 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 152 177 (accept_3_4 22
  152 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 152 177
  (Polychromatic418967fa.accept_9_3_8_6_1_80 21 152 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 152 177 (Polychromatic418967fa.accept_9_2_8_6_1_79 20 152 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 152 177 (accept_3_4 19 152 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 152 177 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 152 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 152 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 17
  152 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 152 177 (accept_3_4 16
  152 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 152 177
  (Polychromatic418967fa.accept_10_5_2_7_1_345 15 152 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 152 177 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 152 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 152 177 (accept_3_4 13 152 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 152 177 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 152 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 152 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 11
  152 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 152 177 (accept_3_4 10
  152 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 152 177
  (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 152 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 152 177 (Polychromatic418967fa.accept_17_8_16_7_1_8792 8 152 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 152 177 (accept_3_4 7 152 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 152 177 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 152 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 152 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 5
  152 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 152 177 (accept_3_4 4 152
  177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 152 177 (Polychromatic418967fa.accept_7_3_5_2_1_17
  3 152 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 152 177
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 152 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 152 177 (accept_3_4 1 152 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152
  177)))))))))))))))))))))))))) (allB_succ' 27 151 177 (Eq.refl Bool.true) (allA_succ_of_accept 26 151 177 (accept_3_5
  26 151 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 151 177
  (Polychromatic418967fa.accept_20_5_11_17_1_5466 25 151 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 151 177 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 151 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 151 177 (accept_3_5 23 151 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 151 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 151 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 151 177
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 151 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 151 177 (accept_3_5 20 151 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 151 177 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 151 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 151 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 151 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 151 177 (accept_3_5 17 151 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 151 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 151 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 151 177
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 15 151 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 151 177 (accept_3_5 14 151 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 151 177 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 151 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 151 177 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 151 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 151 177 (accept_3_5 11 151 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 151 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 151 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 151 177
  (Polychromatic418967fa.accept_17_9_15_7_1_6212 9 151 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 151 177 (accept_3_5 8 151 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  151 177 (Polychromatic418967fa.accept_19_7_18_6_1_3095 7 151 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 151 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 151 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 151 177 (accept_3_5 5 151 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 151 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 151 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 151 177
  (Polychromatic418967fa.accept_9_3_7_6_1_76 3 151 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 151 177 (accept_3_5 2 151 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  151 177 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 151 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 151 177))))))))))))))))))))))))))) (allB_succ' 28 150 177 (Eq.refl Bool.true) (allA_succ_of_gcd
  27 150 177 3 9 50 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 150 177 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 150 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 150 177 (Polychromatic418967fa.accept_13_12_7_8_1_1104 25 150
  177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 150 177 3 8 50 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 150 177
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 150 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 150 177 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 150 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 150 177 3 7 50 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 150 177 (Polychromatic418967fa.accept_7_6_3_2_1_461 20
  150 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 150 177
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 150 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 150 177 3 6 50 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 150 177 (Polychromatic418967fa.accept_11_6_7_1_1_564 17 150 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 150 177 (Polychromatic418967fa.accept_12_4_6_9_1_548 16 150
  177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 150 177 3 5 50 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 150 177
  (Polychromatic418967fa.accept_12_2_6_9_1_19 14 150 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 150 177 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 150 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 150 177 3 4 50 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 150 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 11
  150 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 150 177
  (Polychromatic418967fa.accept_12_10_6_9_1_549 10 150 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 150 177 3 3 50 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 150 177 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 150 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 150 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 150 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 150 177 3 2 50 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 150 177
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 150 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 150 177 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 150 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 150 177 3 1 50 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 150 177 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 150 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 150 177
  (Polychromatic418967fa.accept_7_1_3_2_1_13 1 150 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 150 177)))))))))))))))))))))))))))) (allB_succ' 29 149 177 (Eq.refl Bool.true) (allA_succ_of_accept 28 149
  177 (accept_3_4 28 149 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 149 177
  (Polychromatic418967fa.accept_11_5_6_1_1_988 27 149 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 149 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 149 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 149 177 (accept_3_4 25 149 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 149 177 (Polychromatic418967fa.accept_13_11_6_8_1_1121 24 149 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 149 177
  (Polychromatic418967fa.accept_17_6_13_7_1_272 23 149 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 149 177 (accept_3_4 22 149 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 149 177 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 149 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 149 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 149 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 149 177 (accept_3_4 19 149 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 149 177 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 149 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 149 177
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 149 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 149 177 (accept_3_4 16 149 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 149 177 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 149 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 149 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 149 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 149 177 (accept_3_4 13 149 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 149 177 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 149 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 149 177
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 149 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 149 177 (accept_3_4 10 149 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  149 177 (Polychromatic418967fa.accept_15_9_14_12_1_913 9 149 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 149 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 149 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 149 177 (accept_3_4 7 149 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 149 177 (Polychromatic418967fa.accept_16_6_5_1_1_7761 6 149 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 149 177
  (Polychromatic418967fa.accept_11_5_6_1_1_988 5 149 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 149 177 (accept_3_4 4 149 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  149 177 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 149 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 149 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 149 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 149 177 (accept_3_4 1 149 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 149 177))))))))))))))))))))))))))))) (allB_succ' 30 148 177 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 148 177 (accept_3_5 29 148 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 148 177 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 148 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 148 177 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 148 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 148 177 (accept_3_5 26 148 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 148 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 148 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 148 177
  (Polychromatic418967fa.accept_7_3_1_2_1_247 24 148 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 148 177 (accept_3_5 23 148 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 148 177 (Polychromatic418967fa.accept_17_5_12_7_1_2651 22 148 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 148 177 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 148 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 148 177 (accept_3_5 20 148 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 148 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 148 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 148 177
  (Polychromatic418967fa.accept_12_6_4_9_1_544 18 148 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 148 177 (accept_3_5 17 148 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 148 177 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 148 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 148 177 (Polychromatic418967fa.accept_10_5_8_7_1_2174 15 148 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 148 177 (accept_3_5 14 148 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 148 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 148 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 148 177
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 148 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 148 177 (accept_3_5 11 148 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 148 177 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 148 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 148 177 (Polychromatic418967fa.accept_10_9_8_7_1_714 9 148 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 148 177 (accept_3_5 8 148 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 148 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 148 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 148 177
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 148 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 148 177 (accept_3_5 5 148 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  148 177 (Polychromatic418967fa.accept_17_4_12_7_1_8771 4 148 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 148 177 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 148 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 148 177 (accept_3_5 2 148 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 148 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 148 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 148 177)))))))))))))))))))))))))))))) (allB_succ' 31 147
  177 (Eq.refl Bool.true) (allA_succ_of_gcd 30 147 177 3 10 49 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 147 177 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 147 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 147 177
  (Polychromatic418967fa.accept_9_1_3_6_1_70 28 147 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 147 177 3 9 49 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 147 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 147 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 147 177 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 147 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 147 177 3 8 49 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 147 177
  (Polychromatic418967fa.accept_9_5_3_6_1_269 23 147 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 147 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 147 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 147 177 3 7 49 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 147 177 (Polychromatic418967fa.accept_9_2_3_6_1_88 20
  147 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 177
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 147 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 147 177 3 6 49 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 147 177 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 147 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 147 177 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 147 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 147 177 3 5 49 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 147 177
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 147 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 147 177 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 147 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 147 177 3 4 49 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 147 177 (Polychromatic418967fa.accept_9_2_3_6_1_88 11
  147 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 147 177
  (Polychromatic418967fa.accept_4_2_3_1_1_2 10 147 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 147 177 3 3 49 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 147 177 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 147 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 177 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 147 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 147 177 3 2 49 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 147 177
  (Polychromatic418967fa.accept_9_5_3_6_1_269 5 147 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 147 177 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 147 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 147 177 3 1 49 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 147 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 147 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 177
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 147 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 147 177))))))))))))))))))))))))))))))) (allB_succ' 32 146 177 (Eq.refl Bool.true) (allA_succ_of_accept 31
  146 177 (accept_3_4 31 146 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 146 177
  (Polychromatic418967fa.accept_9_3_2_6_1_264 30 146 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 146 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 146 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 146 177 (accept_3_4 28 146 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 146 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 146 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 146 177 (Polychromatic418967fa.accept_9_8_2_6_1_875
  26 146 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 146 177 (accept_3_4 25
  146 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 146 177
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 146 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 146 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 146 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 146 177 (accept_3_4 22 146 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 146 177 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 146 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 146 177 (Polychromatic418967fa.accept_13_7_3_8_1_1750
  20 146 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 146 177 (accept_3_4 19
  146 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 146 177
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 146 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 146 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 146 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 146 177 (accept_3_4 16 146 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 146 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 146 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 146 177 (Polychromatic418967fa.accept_9_5_2_6_1_265
  14 146 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 146 177 (accept_3_4 13
  146 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 146 177
  (Polychromatic418967fa.accept_9_3_2_6_1_264 12 146 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 146 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 146 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 146 177 (accept_3_4 10 146 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 146 177 (Polychromatic418967fa.accept_13_9_3_8_1_573 9 146 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 146 177 (Polychromatic418967fa.accept_7_1_6_2_1_18 8
  146 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 146 177 (accept_3_4 7 146
  177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 146 177
  (Polychromatic418967fa.accept_12_6_2_9_1_537 6 146 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 146 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 146 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 146 177 (accept_3_4 4 146 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 146 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 146 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 146 177 (Polychromatic418967fa.accept_11_2_3_1_1_244 2
  146 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 146 177 (accept_3_4 1 146
  177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146 177)))))))))))))))))))))))))))))))) (allB_succ' 33 145 177
  (Eq.refl Bool.true) (allA_succ_of_accept 32 145 177 (accept_3_5 32 145 177 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 145 177 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 145 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 145 177 (Polychromatic418967fa.accept_9_3_1_6_1_86 30 145 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 145 177 (accept_3_5 29 145 177
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 145 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 28
  145 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 145 177
  (Polychromatic418967fa.accept_12_3_1_9_1_202 27 145 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 145 177 (accept_3_5 26 145 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 145 177 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 145 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 145 177 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 145 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 145 177 (accept_3_5 23 145 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 145 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 145 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 145 177
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 145 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 145 177 (accept_3_5 20 145 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 145 177 (Polychromatic418967fa.accept_13_6_2_8_1_1782 19 145 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 145 177 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 145 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 145 177 (accept_3_5 17 145 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 145 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 145 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 145 177
  (Polychromatic418967fa.accept_12_3_1_9_1_202 15 145 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 145 177 (accept_3_5 14 145 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 145 177 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 145 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 145 177 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 145 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 145 177 (accept_3_5 11 145 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 145 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 145 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 145 177
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 9 145 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 145 177 (accept_3_5 8 145 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  145 177 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 145 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 145 177 (Polychromatic418967fa.accept_13_6_2_8_1_1782 6 145 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 145 177 (accept_3_5 5 145 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 145 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 145 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 145 177
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 145 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 145 177 (accept_3_5 2 145 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  145 177 (Polychromatic418967fa.accept_25_1_20_2_1_9997 1 145 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 145 177))))))))))))))))))))))))))))))))) (allB_succ' 34 144 177 (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 144 177 3 11 48 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 144 177 (Polychromatic418967fa.accept_10_2_4_7_1_352 32 144 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 144 177 (Polychromatic418967fa.accept_10_1_4_7_1_374
  31 144 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 144 177 3 10 48 59
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 144 177
  (Polychromatic418967fa.accept_15_14_9_12_1_2498 29 144 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 144 177 (Polychromatic418967fa.accept_21_7_18_9_1_5291 28 144 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 144 177 3 9 48 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 144 177
  (Polychromatic418967fa.accept_7_5_4_2_1_235 26 144 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 144 177 (Polychromatic418967fa.accept_13_12_1_8_1_1779 25 144 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 144 177 3 8 48 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 144 177 (Polychromatic418967fa.accept_10_3_4_7_1_353
  23 144 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 144 177
  (Polychromatic418967fa.accept_10_2_4_7_1_352 22 144 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 144 177 3 7 48 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 144 177 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 144 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 144 177 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 144 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 144 177 3 6 48 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 144 177
  (Polychromatic418967fa.accept_19_17_11_6_1_9996 17 144 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 144 177 (Polychromatic418967fa.accept_14_2_4_9_1_2121 16 144 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 144 177 3 5 48 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 144 177
  (Polychromatic418967fa.accept_15_14_9_12_1_2498 14 144 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 144 177 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 144 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 144 177 3 4 48 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 144 177
  (Polychromatic418967fa.accept_10_1_4_7_1_374 11 144 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 144 177 (Polychromatic418967fa.accept_15_10_9_12_1_2497 10 144 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 144 177 3 3 48 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 144 177 (Polychromatic418967fa.accept_21_8_18_9_1_5329
  8 144 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 144 177
  (Polychromatic418967fa.accept_13_7_1_8_1_1778 7 144 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 144 177 3 2 48 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 144 177 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 144 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 144 177 (Polychromatic418967fa.accept_15_4_9_12_1_2495 4 144
  177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 144 177 3 1 48 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 144 177
  (Polychromatic418967fa.accept_10_2_4_7_1_352 2 144 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 144 177 (Polychromatic418967fa.accept_10_1_4_7_1_374 1 144 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 144 177)))))))))))))))))))))))))))))))))) (allB_succ' 35 143 177 (Eq.refl
  Bool.true) (allA_succ_of_accept 34 143 177 (accept_3_4 34 143 177 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 143 177 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 143 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 143 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 143 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 143 177 (accept_3_4 31 143 177
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 143 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 30
  143 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 143 177
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 143 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 143 177 (accept_3_4 28 143 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 143 177 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 143 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 143 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 143 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 143 177 (accept_3_4 25 143 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 143 177 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 143 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 143 177
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 143 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 143 177 (accept_3_4 22 143 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 143 177 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 143 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 143 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 143 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 143 177 (accept_3_4 19 143 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 143 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 143 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 143 177
  (Polychromatic418967fa.accept_27_17_8_15_1_2268 17 143 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 143 177 (accept_3_4 16 143 177 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 143 177 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 143 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 143 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 143 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 143 177 (accept_3_4 13 143 177
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 143 177 (Polychromatic418967fa.accept_7_5_3_2_1_249
  12 143 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 143 177
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 143 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 143 177 (accept_3_4 10 143 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  143 177 (Polychromatic418967fa.accept_18_9_17_15_1_2267 9 143 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 143 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 143 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 143 177 (accept_3_4 7 143 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 143 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 143 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 143 177
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 143 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 143 177 (accept_3_4 4 143 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  143 177 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 143 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 143 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 143 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 143 177 (accept_3_4 1 143 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 143 177))))))))))))))))))))))))))))))))))) (allB_succ' 36 142 177 (Eq.refl Bool.true)
  (allA_succ_of_accept 35 142 177 (accept_3_5 35 142 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 142 177 (Polychromatic418967fa.accept_10_4_2_7_1_373 34 142 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 142 177 (Polychromatic418967fa.accept_13_7_12_8_1_199 33 142 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 142 177 (accept_3_5 32 142 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 142 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 142 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 142 177
  (Polychromatic418967fa.accept_9_3_7_6_1_76 30 142 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 142 177 (accept_3_5 29 142 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 142 177 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 142 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 142 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 142 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 142 177 (accept_3_5 26 142 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 142 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 142 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 142 177
  (Polychromatic418967fa.accept_10_4_2_7_1_373 24 142 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 142 177 (accept_3_5 23 142 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 142 177 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 142 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 142 177 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 142 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 142 177 (accept_3_5 20 142 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 142 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 142 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 142 177
  (Polychromatic418967fa.accept_12_6_10_9_1_531 18 142 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 142 177 (accept_3_5 17 142 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 142 177 (Polychromatic418967fa.accept_17_16_6_7_1_2715 16 142 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 142 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 142 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 142 177 (accept_3_5 14 142 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 142 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 142 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 142 177
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 142 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 142 177 (accept_3_5 11 142 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 142 177 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 142 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 142 177 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 142 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 142 177 (accept_3_5 8 142 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 142 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 142 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 142 177
  (Polychromatic418967fa.accept_12_6_10_9_1_531 6 142 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 142 177 (accept_3_5 5 142 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  142 177 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 142 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 142 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 142 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 142 177 (accept_3_5 2 142 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 142 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 142 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142 177)))))))))))))))))))))))))))))))))))) (allB_succ'
  37 141 177 (Eq.refl Bool.true) (allA_succ_of_gcd 36 141 177 3 12 47 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 141 177 (Polychromatic418967fa.accept_13_9_11_8_1_195
  35 141 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 141 177
  (Polychromatic418967fa.accept_7_6_1_2_1_230 34 141 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 141 177 3 11 47 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 141 177 (Polychromatic418967fa.accept_11_10_9_1_1_2186 32 141 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 141 177
  (Polychromatic418967fa.accept_7_3_1_2_1_247 31 141 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 141 177 3 10 47 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 141 177 (Polychromatic418967fa.accept_13_3_11_8_1_1094 29 141 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 141 177
  (Polychromatic418967fa.accept_8_4_5_1_1_299 28 141 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 141 177 3 9 47 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 141 177 (Polychromatic418967fa.accept_10_6_1_7_1_342 26 141 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 177 (Polychromatic418967fa.accept_15_10_6_12_1_1645 25 141
  177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 141 177 3 8 47 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 141 177
  (Polychromatic418967fa.accept_13_10_11_8_1_1770 23 141 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 141 177 (Polychromatic418967fa.accept_13_9_11_8_1_195 22 141 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 141 177 3 7 47 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 141 177
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 141 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 141 177 (Polychromatic418967fa.accept_13_6_11_8_1_1111 19 141 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 141 177 3 6 47 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 141 177 (Polychromatic418967fa.accept_7_3_1_2_1_247 17
  141 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 141 177
  (Polychromatic418967fa.accept_10_6_1_7_1_342 16 141 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 141 177 3 5 47 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 141 177 (Polychromatic418967fa.accept_10_4_1_7_1_371 14 141 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 177 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 141 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 141 177 3 4 47 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 141 177
  (Polychromatic418967fa.accept_17_11_5_7_1_6177 11 141 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 141 177 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 141 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 141 177 3 3 47 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 141 177 (Polychromatic418967fa.accept_14_8_1_9_1_2085 8 141 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 177
  (Polychromatic418967fa.accept_15_7_6_12_1_1614 7 141 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 141 177 3 2 47 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 141 177 (Polychromatic418967fa.accept_15_5_6_12_1_916 5 141 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 177 (Polychromatic418967fa.accept_8_4_5_1_1_299 4 141 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 141 177 3 1 47 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 141 177
  (Polychromatic418967fa.accept_15_2_6_12_1_1613 2 141 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 141 177 (Polychromatic418967fa.accept_13_1_11_8_1_2562 1 141 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 141 177))))))))))))))))))))))))))))))))))))) (allB_succ' 38 140 177 (Eq.refl
  Bool.true) (allA_succ_of_accept 37 140 177 (accept_3_4 37 140 177 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 140 177 (Polychromatic418967fa.accept_15_6_5_12_1_1642 36 140 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 140 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 140 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 140 177 (accept_3_4 34 140 177
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 140 177 (Polychromatic418967fa.accept_13_7_10_8_1_567
  33 140 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 140 177
  (Polychromatic418967fa.accept_15_2_5_12_1_369 32 140 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 140 177 (accept_3_4 31 140 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 140 177 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 140 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 140 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 140 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 140 177 (accept_3_4 28 140 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 140 177 (Polychromatic418967fa.accept_16_11_12_1_1_3001 27 140 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 140 177
  (Polychromatic418967fa.accept_9_8_5_6_1_538 26 140 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 140 177 (accept_3_4 25 140 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 140 177 (Polychromatic418967fa.accept_13_11_10_8_1_1804 24 140 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 140 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 140 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 140 177 (accept_3_4 22 140 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 140 177 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 140 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 140 177
  (Polychromatic418967fa.accept_9_2_5_6_1_536 20 140 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 140 177 (accept_3_4 19 140 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 140 177 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 140 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 140 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 140 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 140 177 (accept_3_4 16 140 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 140 177 (Polychromatic418967fa.accept_11_4_8_1_1_1047 15 140 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 140 177
  (Polychromatic418967fa.accept_17_14_4_7_1_7439 14 140 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 140 177 (accept_3_4 13 140 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 140 177 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 140 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 140 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 140 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 140 177 (accept_3_4 10 140 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 140 177 (Polychromatic418967fa.accept_15_9_5_12_1_1640 9 140 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 140 177
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 140 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 140 177 (accept_3_4 7 140 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  140 177 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 140 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 140 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 140 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 140 177 (accept_3_4 4 140 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 140 177 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 140 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 140 177
  (Polychromatic418967fa.accept_9_2_5_6_1_536 2 140 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 140 177 (accept_3_4 1 140 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140
  177)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 139 177 (Eq.refl Bool.true) (allA_succ_of_accept 38 139 177
  (accept_3_5 38 139 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 139 177
  (Polychromatic418967fa.accept_9_1_4_6_1_5 37 139 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 139 177 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 139 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 139 177 (accept_3_5 35 139 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 139 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 139 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 139 177 (Polychromatic418967fa.accept_13_7_9_8_1_188
  33 139 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 139 177 (accept_3_5 32
  139 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 139 177
  (Polychromatic418967fa.accept_7_3_6_2_1_90 31 139 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 139 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 139 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 139 177 (accept_3_5 29 139 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 139 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 139 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 139 177 (Polychromatic418967fa.accept_12_3_7_9_1_1009
  27 139 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 139 177 (accept_3_5 26
  139 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 139 177
  (Polychromatic418967fa.accept_7_4_6_2_1_451 25 139 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 139 177 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 139 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 139 177 (accept_3_5 23 139 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 139 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 139 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 139 177 (Polychromatic418967fa.accept_9_3_4_6_1_252
  21 139 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 139 177 (accept_3_5 20
  139 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 139 177
  (Polychromatic418967fa.accept_9_1_4_6_1_5 19 139 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 139 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 139 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 139 177 (accept_3_5 17 139 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 139 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 139 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 139 177 (Polychromatic418967fa.accept_7_1_6_2_1_18 15
  139 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 139 177 (accept_3_5 14
  139 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 139 177
  (Polychromatic418967fa.accept_25_13_14_2_1_9995 13 139 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 139 177 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 139 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 139 177 (accept_3_5 11 139 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 139 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 139 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 139 177
  (Polychromatic418967fa.accept_15_9_4_12_1_1611 9 139 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 139 177 (accept_3_5 8 139 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  139 177 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 139 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 139 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 139 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 139 177 (accept_3_5 5 139 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 139 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 139 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 139 177
  (Polychromatic418967fa.accept_7_3_6_2_1_90 3 139 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 139 177 (accept_3_5 2 139 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  139 177 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 139 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 139 177))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 138 177 (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 138 177 3 13 46 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 138 177 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 138 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 138 177 (Polychromatic418967fa.accept_9_1_3_6_1_70 37
  138 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 138 177 3 12 46 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 138 177
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 138 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 138 177 (Polychromatic418967fa.accept_9_7_3_6_1_270 34 138 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 138 177 3 11 46 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 138 177 (Polychromatic418967fa.accept_7_4_5_2_1_243 32
  138 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 138 177
  (Polychromatic418967fa.accept_4_3_2_1_1_50 31 138 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 138 177 3 10 46 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 138 177 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 138 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 138 177 (Polychromatic418967fa.accept_9_1_3_6_1_70 28
  138 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 138 177 3 9 46 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 138 177
  (Polychromatic418967fa.accept_9_8_3_6_1_533 26 138 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 138 177 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 138 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 138 177 3 8 46 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 138 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 23
  138 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 138 177
  (Polychromatic418967fa.accept_9_4_3_6_1_532 22 138 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 138 177 3 7 46 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 138 177 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 138 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 138 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 138 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 138 177 3 6 46 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 138 177
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 138 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 138 177 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 138 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 138 177 3 5 46 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 138 177 (Polychromatic418967fa.accept_9_5_3_6_1_269 14
  138 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 138 177
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 138 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 138 177 3 4 46 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 138 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 138 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 138 177 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 138 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 138 177 3 3 46 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 138 177
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 138 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 138 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 138 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 138 177 3 2 46 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 138 177 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 138 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 138 177
  (Polychromatic418967fa.accept_7_4_5_2_1_243 4 138 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 138 177 3 1 46 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 138 177 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 138 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 138 177 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 138 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138 177))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 41 137 177 (Eq.refl Bool.true) (allA_succ_of_accept 40 137 177 (accept_3_4 40 137 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 137 177 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 137 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 137 177
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 137 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 137 177 (accept_3_4 37 137 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 137 177 (Polychromatic418967fa.accept_13_10_7_8_1_1794 36 137 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 137 177 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 137 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 137 177 (accept_3_4 34 137 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 137 177 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 137 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 137 177
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 137 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 137 177 (accept_3_4 31 137 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 137 177 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 137 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 137 177 (Polychromatic418967fa.accept_13_3_7_8_1_4192 29 137 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 137 177 (accept_3_4 28 137 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 137 177 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 137 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 137 177
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 137 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 137 177 (accept_3_4 25 137 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 137 177 (Polychromatic418967fa.accept_16_8_9_1_1_7753 24 137 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 137 177 (Polychromatic418967fa.accept_9_5_2_6_1_265 23 137 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 137 177 (accept_3_4 22 137 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 137 177 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 137 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 137 177
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 137 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 137 177 (accept_3_4 19 137 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 137 177 (Polychromatic418967fa.accept_15_3_2_12_1_2469 18 137 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 137 177 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 137 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 137 177 (accept_3_4 16 137 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 137 177 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 137 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 137 177
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 137 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 137 177 (accept_3_4 13 137 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 137 177 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 137 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 137 177 (Polychromatic418967fa.accept_17_11_1_7_1_2657 11 137 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 137 177 (accept_3_4 10 137 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 137 177 (Polychromatic418967fa.accept_13_9_7_8_1_1122 9 137 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 177
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 137 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 137 177 (accept_3_4 7 137 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  137 177 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 137 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 137 177 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 137 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 177 (accept_3_4 4 137 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 137 177 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 137 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 137 177
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 137 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 137 177 (accept_3_4 1 137 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 137
  177))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 136 177 (Eq.refl Bool.true) (allA_succ_of_accept 41 136
  177 (accept_3_5 41 136 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 136 177
  (Polychromatic418967fa.accept_7_5_3_2_1_249 40 136 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 136 177 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 136 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 136 177 (accept_3_5 38 136 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 136 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 136 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 136 177 (Polychromatic418967fa.accept_7_1_3_2_1_13 36
  136 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 136 177 (accept_3_5 35
  136 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 136 177
  (Polychromatic418967fa.accept_7_6_3_2_1_461 34 136 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 136 177 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 136 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 136 177 (accept_3_5 32 136 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 136 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 136 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 136 177 (Polychromatic418967fa.accept_9_3_1_6_1_86 30
  136 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 136 177 (accept_3_5 29
  136 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 136 177
  (Polychromatic418967fa.accept_13_2_6_8_1_1092 28 136 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 136 177 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 136 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 136 177 (accept_3_5 26 136 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 136 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 136 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 136 177
  (Polychromatic418967fa.accept_13_11_6_8_1_1121 24 136 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 136 177 (accept_3_5 23 136 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 136 177 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 136 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 136 177 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 136 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 136 177 (accept_3_5 20 136 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 136 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 136 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 136 177
  (Polychromatic418967fa.accept_12_6_4_9_1_544 18 136 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 136 177 (accept_3_5 17 136 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 136 177 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 136 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 136 177 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 136 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 136 177 (accept_3_5 14 136 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 136 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 136 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 136 177
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 136 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 136 177 (accept_3_5 11 136 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 136 177 (Polychromatic418967fa.accept_25_10_11_2_1_9994 10 136 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 136 177 (Polychromatic418967fa.accept_16_9_8_1_1_1228 9 136 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 136 177 (accept_3_5 8 136 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 136 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 136 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 136 177
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 136 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 136 177 (accept_3_5 5 136 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  136 177 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 136 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 136 177 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 136 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 136 177 (accept_3_5 2 136 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 136 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 136 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 136 177))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 43 135 177 (Eq.refl Bool.true) (allA_succ_of_gcd 42 135 177 3 14 45 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 135 177
  (Polychromatic418967fa.accept_12_5_3_9_1_541 41 135 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 135 177 (Polychromatic418967fa.accept_13_1_5_8_1_207 40 135 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 135 177 3 13 45 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 135 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 38
  135 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 135 177
  (Polychromatic418967fa.accept_12_1_3_9_1_174 37 135 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 135 177 3 12 45 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 135 177 (Polychromatic418967fa.accept_11_2_3_1_1_244 35 135 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 135 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 34
  135 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 135 177 3 11 45 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 135 177
  (Polychromatic418967fa.accept_10_2_5_7_1_1124 32 135 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 135 177 (Polychromatic418967fa.accept_12_7_3_9_1_999 31 135 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 135 177 3 10 45 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 135 177 (Polychromatic418967fa.accept_12_5_3_9_1_541
  29 135 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 135 177
  (Polychromatic418967fa.accept_10_8_5_7_1_358 28 135 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 135 177 3 9 45 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 135 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 135 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 135 177 (Polychromatic418967fa.accept_12_1_3_9_1_174 25 135
  177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 135 177 3 8 45 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 135 177
  (Polychromatic418967fa.accept_10_3_5_7_1_330 23 135 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 135 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 135 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 135 177 3 7 45 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 135 177 (Polychromatic418967fa.accept_17_3_16_7_1_5014
  20 135 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 135 177
  (Polychromatic418967fa.accept_12_7_3_9_1_999 19 135 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 135 177 3 6 45 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 135 177 (Polychromatic418967fa.accept_12_5_3_9_1_541 17 135 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 135 177 (Polychromatic418967fa.accept_13_3_5_8_1_1099 16 135
  177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 135 177 3 5 45 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 135 177
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 135 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 135 177 (Polychromatic418967fa.accept_10_3_5_7_1_330 13 135 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 135 177 3 4 45 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 135 177 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  11 135 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 135 177
  (Polychromatic418967fa.accept_4_2_3_1_1_2 10 135 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 135 177 3 3 45 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 135 177 (Polychromatic418967fa.accept_10_8_5_7_1_358 8 135 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 177 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 135 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 135 177 3 2 45 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 135 177
  (Polychromatic418967fa.accept_12_5_3_9_1_541 5 135 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 135 177 (Polychromatic418967fa.accept_18_4_9_15_1_3383 4 135 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 135 177 3 1 45 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 135 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 135 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 177
  (Polychromatic418967fa.accept_12_1_3_9_1_174 1 135 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 135 177))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 134 177 (Eq.refl Bool.true)
  (allA_succ_of_accept 43 134 177 (accept_3_4 43 134 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 134 177 (Polychromatic418967fa.accept_10_2_4_7_1_352 42 134 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 134 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 134 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 134 177 (accept_3_4 40 134 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 134 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 134 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 134 177
  (Polychromatic418967fa.accept_7_3_1_2_1_247 38 134 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 134 177 (accept_3_4 37 134 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 134 177 (Polychromatic418967fa.accept_11_3_2_1_1_994 36 134 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 134 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 134 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 134 177 (accept_3_4 34 134 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 134 177 (Polychromatic418967fa.accept_10_3_4_7_1_353 33 134 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 134 177
  (Polychromatic418967fa.accept_9_5_8_6_1_281 32 134 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 134 177 (accept_3_4 31 134 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 134 177 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 134 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 134 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 134 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 134 177 (accept_3_4 28 134 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 134 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 134 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 134 177
  (Polychromatic418967fa.accept_15_11_14_12_1_2458 26 134 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 134 177 (accept_3_4 25 134 177 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 134 177 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 134 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 134 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 134 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 134 177 (accept_3_4 22 134 177
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 134 177 (Polychromatic418967fa.accept_9_3_8_6_1_80 21
  134 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 134 177
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 134 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 134 177 (accept_3_4 19 134 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 134 177 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 134 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 134 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 134 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 134 177 (accept_3_4 16 134 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 134 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 134 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 134 177
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 134 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 134 177 (accept_3_4 13 134 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 134 177 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 134 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 134 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 134 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 134 177 (accept_3_4 10 134 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 134 177 (Polychromatic418967fa.accept_13_9_4_8_1_1752 9 134 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 134 177
  (Polychromatic418967fa.accept_24_8_14_9_1_9993 8 134 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 134 177 (accept_3_4 7 134 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  134 177 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 134 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 134 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 134 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 134 177 (accept_3_4 4 134 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 134 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 134 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 134 177
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 134 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 134 177 (accept_3_4 1 134 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134
  177)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 133 177 (Eq.refl Bool.true) (allA_succ_of_accept 44 133
  177 (accept_3_5 44 133 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 133 177
  (Polychromatic418967fa.accept_27_16_25_15_1_9992 43 133 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 133 177 (Polychromatic418967fa.accept_17_8_14_7_1_6203 42 133 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 133 177 (accept_3_5 41 133 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 133 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 133 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 133 177
  (Polychromatic418967fa.accept_9_3_7_6_1_76 39 133 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 133 177 (accept_3_5 38 133 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 133 177 (Polychromatic418967fa.accept_9_1_7_6_1_75 37 133 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 133 177 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 133 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 133 177 (accept_3_5 35 133 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 133 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 133 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 133 177
  (Polychromatic418967fa.accept_13_7_3_8_1_1750 33 133 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 133 177 (accept_3_5 32 133 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 133 177 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 133 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 133 177 (Polychromatic418967fa.accept_9_3_7_6_1_76 30 133 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 133 177 (accept_3_5 29 133 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 133 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 133 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 133 177
  (Polychromatic418967fa.accept_12_3_1_9_1_202 27 133 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 133 177 (accept_3_5 26 133 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 133 177 (Polychromatic418967fa.accept_10_5_3_7_1_1108 25 133 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 133 177 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 133 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 133 177 (accept_3_5 23 133 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 133 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 133 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 133 177
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 133 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 133 177 (accept_3_5 20 133 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 133 177 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 133 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 133 177 (Polychromatic418967fa.accept_13_5_3_8_1_1117 18 133 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 133 177 (accept_3_5 17 133 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 133 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 133 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 133 177
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 133 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 133 177 (accept_3_5 14 133 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 133 177 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 133 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 133 177 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 133 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 133 177 (accept_3_5 11 133 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 133 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 133 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 133 177
  (Polychromatic418967fa.accept_13_9_3_8_1_573 9 133 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 133 177 (accept_3_5 8 133 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  133 177 (Polychromatic418967fa.accept_13_7_3_8_1_1750 7 133 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 133 177 (Polychromatic418967fa.accept_10_6_3_7_1_2197 6 133 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 133 177 (accept_3_5 5 133 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 133 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 133 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 133 177
  (Polychromatic418967fa.accept_9_3_7_6_1_76 3 133 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 133 177 (accept_3_5 2 133 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  133 177 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 133 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 133 177))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 132 177 (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 132 177 3 15 44 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 132 177 (Polychromatic418967fa.accept_10_4_2_7_1_373 44 132 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 132 177 (Polychromatic418967fa.accept_7_1_6_2_1_18 43
  132 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 132 177 3 14 44 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 132 177
  (Polychromatic418967fa.accept_18_5_6_15_1_3413 41 132 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 132 177 (Polychromatic418967fa.accept_16_8_4_1_1_2102 40 132 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 132 177 3 13 44 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 132 177 (Polychromatic418967fa.accept_7_3_6_2_1_90 38
  132 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 132 177
  (Polychromatic418967fa.accept_8_5_4_1_1_111 37 132 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 132 177 3 12 44 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 132 177 (Polychromatic418967fa.accept_10_5_2_7_1_345 35 132 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 132 177 (Polychromatic418967fa.accept_10_4_2_7_1_373
  34 132 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 132 177 3 11 44 59
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 132 177
  (Polychromatic418967fa.accept_7_4_6_2_1_451 32 132 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 132 177 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 132 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 132 177 3 10 44 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 132 177 (Polychromatic418967fa.accept_7_1_6_2_1_18 29
  132 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 132 177
  (Polychromatic418967fa.accept_16_12_4_1_1_1257 28 132 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 132 177 3 9 44 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 132 177 (Polychromatic418967fa.accept_19_7_18_6_1_3095 26 132 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 132 177 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 132 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 132 177 3 8 44 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 132 177
  (Polychromatic418967fa.accept_13_10_2_8_1_2603 23 132 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 132 177 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 132 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 132 177 3 7 44 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 132 177 (Polychromatic418967fa.accept_13_7_2_8_1_1746
  20 132 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 132 177
  (Polychromatic418967fa.accept_10_9_2_7_1_1096 19 132 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 132 177 3 6 44 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 132 177 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 132 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 132 177 (Polychromatic418967fa.accept_18_16_6_15_1_3376 16 132
  177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 132 177 3 5 44 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 132 177
  (Polychromatic418967fa.accept_10_4_2_7_1_373 14 132 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 132 177 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 132 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 132 177 3 4 44 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 132 177 (Polychromatic418967fa.accept_7_4_6_2_1_451 11
  132 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 132 177
  (Polychromatic418967fa.accept_7_3_6_2_1_90 10 132 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 132 177 3 3 44 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 132 177 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 132 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 132 177 (Polychromatic418967fa.accept_13_7_2_8_1_1746 7 132 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132 177 3 2 44 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 132 177
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 132 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 132 177 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 132 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 132 177 3 1 44 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 132 177 (Polychromatic418967fa.accept_17_2_13_7_1_5011 2 132 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 132 177
  (Polychromatic418967fa.accept_7_1_6_2_1_18 1 132 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 132 177)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 131 177 (Eq.refl Bool.true)
  (allA_succ_of_accept 46 131 177 (accept_3_4 46 131 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 131 177 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 131 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 131 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 131 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 131 177 (accept_3_4 43 131 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 131 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 131 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 131 177
  (Polychromatic418967fa.accept_19_3_17_6_1_1991 41 131 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 131 177 (accept_3_4 40 131 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 131 177 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 131 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 131 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 131 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 131 177 (accept_3_4 37 131 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 131 177 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 131 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 131 177
  (Polychromatic418967fa.accept_9_8_5_6_1_538 35 131 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 131 177 (accept_3_4 34 131 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 131 177 (Polychromatic418967fa.accept_13_7_1_8_1_1778 33 131 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 131 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 131 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 131 177 (accept_3_4 31 131 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 131 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 131 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 131 177
  (Polychromatic418967fa.accept_9_2_5_6_1_536 29 131 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 131 177 (accept_3_4 28 131 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 131 177 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 131 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 131 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 131 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 131 177 (accept_3_4 25 131 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 131 177 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 131 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 131 177
  (Polychromatic418967fa.accept_15_8_11_12_1_1626 23 131 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 131 177 (accept_3_4 22 131 177 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 131 177 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 131 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 131 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 131 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 131 177 (accept_3_4 19 131 177
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 131 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 18
  131 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 131 177
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 131 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 131 177 (accept_3_4 16 131 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 131 177 (Polychromatic418967fa.accept_12_3_11_9_1_193 15 131 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 131 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 131 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 131 177 (accept_3_4 13 131 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 131 177 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 131 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 131 177
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 131 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 131 177 (accept_3_4 10 131 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  131 177 (Polychromatic418967fa.accept_11_9_10_1_1_581 9 131 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 131 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 131 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 131 177 (accept_3_4 7 131 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 131 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 131 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 131 177
  (Polychromatic418967fa.accept_13_5_1_8_1_1115 5 131 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 131 177 (accept_3_4 4 131 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  131 177 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 131 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 131 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 131 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 131 177 (accept_3_4 1 131 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 131 177))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 130 177 (Eq.refl
  Bool.true) (allA_succ_of_accept 47 130 177 (accept_3_5 47 130 177 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 130 177 (Polychromatic418967fa.accept_9_1_4_6_1_5 46 130 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 130 177 (Polychromatic418967fa.accept_18_9_4_15_1_555 45 130
  177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 130 177 (accept_3_5 44 130
  177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 130 177
  (Polychromatic418967fa.accept_4_3_2_1_1_50 43 130 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 130 177 (Polychromatic418967fa.accept_12_6_10_9_1_531 42 130 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 130 177 (accept_3_5 41 130 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 130 177 (Polychromatic418967fa.accept_7_5_4_2_1_235 40 130 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 130 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 39
  130 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 130 177 (accept_3_5 38
  130 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 130 177
  (Polychromatic418967fa.accept_6_1_4_3_1_14 37 130 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 130 177 (Polychromatic418967fa.accept_15_6_10_12_1_2538 36 130 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 130 177 (accept_3_5 35 130 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 130 177 (Polychromatic418967fa.accept_7_6_4_2_1_236 34 130 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 130 177
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 130 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 130 177 (accept_3_5 32 130 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 130 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 130 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 130 177 (Polychromatic418967fa.accept_9_3_4_6_1_252 30 130 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 130 177 (accept_3_5 29 130 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 130 177 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 130 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 130 177
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 130 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 130 177 (accept_3_5 26 130 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 130 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 130 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 130 177 (Polychromatic418967fa.accept_15_9_10_12_1_1625 24 130 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 130 177 (accept_3_5 23 130 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 130 177 (Polychromatic418967fa.accept_15_7_10_12_1_2403 22 130
  177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 130 177
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 130 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 130 177 (accept_3_5 20 130 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 130 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 130 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 130 177 (Polychromatic418967fa.accept_12_6_10_9_1_531 18 130 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 130 177 (accept_3_5 17 130 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 130 177 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 130 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 130 177
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 130 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 130 177 (accept_3_5 14 130 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 130 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 130 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 130 177 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 130 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 130 177 (accept_3_5 11 130 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 130 177 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 130 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 130 177
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 9 130 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 130 177 (accept_3_5 8 130 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  130 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 130 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 130 177 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 130 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 130 177 (accept_3_5 5 130 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 130 177 (Polychromatic418967fa.accept_23_4_15_16_1_9991 4 130 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 130 177
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 130 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 130 177 (accept_3_5 2 130 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  130 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 130 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 130 177)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 129 177 (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 129 177 3 16 43 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 129 177 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 129 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 129 177
  (Polychromatic418967fa.accept_9_1_3_6_1_70 46 129 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 129 177 3 15 43 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 129 177 (Polychromatic418967fa.accept_9_8_3_6_1_533 44 129 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 129 177 (Polychromatic418967fa.accept_7_1_3_2_1_13 43
  129 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 129 177 3 14 43 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 129 177
  (Polychromatic418967fa.accept_7_6_3_2_1_461 41 129 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 129 177 (Polychromatic418967fa.accept_7_5_3_2_1_249 40 129 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 129 177 3 13 43 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 129 177 (Polychromatic418967fa.accept_9_2_3_6_1_88 38
  129 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 129 177
  (Polychromatic418967fa.accept_9_1_3_6_1_70 37 129 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 129 177 3 12 43 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 129 177 (Polychromatic418967fa.accept_9_8_3_6_1_533 35 129 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 129 177 (Polychromatic418967fa.accept_7_6_3_2_1_461
  34 129 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 129 177 3 11 43 59
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 129 177
  (Polychromatic418967fa.accept_9_5_3_6_1_269 32 129 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 129 177 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 129 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 129 177 3 10 43 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 129 177 (Polychromatic418967fa.accept_7_1_3_2_1_13 29
  129 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 129 177
  (Polychromatic418967fa.accept_9_1_3_6_1_70 28 129 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 129 177 3 9 43 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 129 177 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 129 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 177 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 129 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 129 177 3 8 43 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 129 177
  (Polychromatic418967fa.accept_9_5_3_6_1_269 23 129 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 129 177 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 129 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 129 177 3 7 43 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 129 177 (Polychromatic418967fa.accept_7_6_3_2_1_461 20
  129 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 177
  (Polychromatic418967fa.accept_7_5_3_2_1_249 19 129 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 129 177 3 6 43 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 129 177 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 129 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 177 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 129 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 129 177 3 5 43 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 129 177
  (Polychromatic418967fa.accept_9_5_3_6_1_269 14 129 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 129 177 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 129 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 129 177 3 4 43 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 129 177 (Polychromatic418967fa.accept_9_2_3_6_1_88 11
  129 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 177
  (Polychromatic418967fa.accept_9_1_3_6_1_70 10 129 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 129 177 3 3 43 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 129 177 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 129 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 177 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 129 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 129 177 3 2 43 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 129 177
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 129 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 129 177 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 129 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 129 177 3 1 43 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 129 177 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 129 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 177
  (Polychromatic418967fa.accept_7_1_3_2_1_13 1 129 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 129 177))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 128 177 (Eq.refl Bool.true)
  (allA_succ_of_accept 49 128 177 (accept_3_4 49 128 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 128 177 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 128 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 128 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 128 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 128 177 (accept_3_4 46 128 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 128 177 (Polychromatic418967fa.accept_10_5_8_7_1_2174 45 128 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 128 177
  (Polychromatic418967fa.accept_9_8_2_6_1_875 44 128 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 128 177 (accept_3_4 43 128 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 128 177 (Polychromatic418967fa.accept_12_6_8_9_1_553 42 128 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 128 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 128 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 128 177 (accept_3_4 40 128 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 128 177 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 128 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 128 177
  (Polychromatic418967fa.accept_21_17_2_9_1_6867 38 128 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 128 177 (accept_3_4 37 128 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 128 177 (Polychromatic418967fa.accept_13_10_11_8_1_1770 36 128 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 128 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 128 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 128 177 (accept_3_4 34 128 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 128 177 (Polychromatic418967fa.accept_15_3_8_12_1_900 33 128 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 128 177
  (Polychromatic418967fa.accept_9_5_2_6_1_265 32 128 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 128 177 (accept_3_4 31 128 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 128 177 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 128 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 128 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 128 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 128 177 (accept_3_4 28 128 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 128 177 (Polychromatic418967fa.accept_13_1_11_8_1_2562 27 128 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 128 177
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 128 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 128 177 (accept_3_4 25 128 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 128 177 (Polychromatic418967fa.accept_19_5_14_6_1_4413 24 128 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 128 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 128 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 128 177 (accept_3_4 22 128 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 128 177 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 128 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 128 177
  (Polychromatic418967fa.accept_15_5_8_12_1_2435 20 128 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 128 177 (accept_3_4 19 128 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 128 177 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 128 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 128 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 128 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 128 177 (accept_3_4 16 128 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 128 177 (Polychromatic418967fa.accept_10_5_8_7_1_2174 15 128 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 128 177
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 128 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 128 177 (accept_3_4 13 128 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 128 177 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 128 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 128 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 128 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 128 177 (accept_3_4 10 128 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 128 177 (Polychromatic418967fa.accept_10_9_8_7_1_714 9 128 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 128 177
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 128 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 128 177 (accept_3_4 7 128 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  128 177 (Polychromatic418967fa.accept_11_6_7_1_1_564 6 128 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 128 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 128 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 128 177 (accept_3_4 4 128 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 128 177 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 128 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 128 177
  (Polychromatic418967fa.accept_17_2_9_7_1_5002 2 128 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 128 177 (accept_3_4 1 128 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128
  177)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 127 177 (Eq.refl Bool.true) (allA_succ_of_accept
  50 127 177 (accept_3_5 50 127 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 127 177
  (Polychromatic418967fa.accept_9_4_1_6_1_284 49 127 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 127 177 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 127 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 127 177 (accept_3_5 47 127 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 127 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 127 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 127 177 (Polychromatic418967fa.accept_7_3_1_2_1_247
  45 127 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 127 177 (accept_3_5 44
  127 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 127 177
  (Polychromatic418967fa.accept_9_7_1_6_1_261 43 127 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 127 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 127 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 127 177 (accept_3_5 41 127 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 127 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 127 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 127 177 (Polychromatic418967fa.accept_9_3_1_6_1_86 39
  127 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 127 177 (accept_3_5 38
  127 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 127 177
  (Polychromatic418967fa.accept_13_11_10_8_1_1804 37 127 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 127 177 (Polychromatic418967fa.accept_14_8_1_9_1_2085 36 127 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 127 177 (accept_3_5 35 127 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 127 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 127 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 127 177
  (Polychromatic418967fa.accept_13_7_10_8_1_567 33 127 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 127 177 (accept_3_5 32 127 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 127 177 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 127 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 127 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 127 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 127 177 (accept_3_5 29 127 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 127 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 127 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 127 177
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 127 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 127 177 (accept_3_5 26 127 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 127 177 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 127 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 127 177 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 127 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 127 177 (accept_3_5 23 127 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 127 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 127 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 127 177
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 127 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 127 177 (accept_3_5 20 127 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 127 177 (Polychromatic418967fa.accept_15_4_7_12_1_5538 19 127 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 127 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 127 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 127 177 (accept_3_5 17 127 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 127 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 127 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 127 177
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 15 127 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 127 177 (accept_3_5 14 127 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 127 177 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 127 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 127 177 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 127 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 127 177 (accept_3_5 11 127 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 127 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 127 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 127 177
  (Polychromatic418967fa.accept_19_9_13_6_1_7198 9 127 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 127 177 (accept_3_5 8 127 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  127 177 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 127 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 127 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 127 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 127 177 (accept_3_5 5 127 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 127 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 127 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 127 177
  (Polychromatic418967fa.accept_7_3_1_2_1_247 3 127 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 127 177 (accept_3_5 2 127 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  127 177 (Polychromatic418967fa.accept_17_1_8_7_1_4982 1 127 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 127 177))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 126 177 (Eq.refl
  Bool.true) (allA_succ_of_gcd 51 126 177 3 17 42 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 50 126 177 (Polychromatic418967fa.accept_11_6_5_1_1_586 50 126 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 126 177
  (Polychromatic418967fa.accept_20_9_6_17_1_1654 49 126 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 126 177 3 16 42 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 126 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 126 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 126 177 (Polychromatic418967fa.accept_12_10_6_9_1_549
  46 126 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 126 177 3 15 42 59
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 126 177
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 44 126 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 126 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 126 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 126 177 3 14 42 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 126 177 (Polychromatic418967fa.accept_10_1_6_7_1_710
  41 126 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 126 177
  (Polychromatic418967fa.accept_12_4_6_9_1_548 40 126 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 126 177 3 13 42 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 126 177 (Polychromatic418967fa.accept_12_2_6_9_1_19 38 126 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 126 177
  (Polychromatic418967fa.accept_13_11_9_8_1_1125 37 126 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 126 177 3 12 42 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 126 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 126 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 126 177 (Polychromatic418967fa.accept_12_10_6_9_1_549
  34 126 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 126 177 3 11 42 59
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 126 177
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 32 126 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 126 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 126 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 126 177 3 10 42 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 126 177 (Polychromatic418967fa.accept_13_3_9_8_1_4202
  29 126 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 126 177
  (Polychromatic418967fa.accept_11_6_5_1_1_586 28 126 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 126 177 3 9 42 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 126 177 (Polychromatic418967fa.accept_12_2_6_9_1_19 26 126 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 126 177 (Polychromatic418967fa.accept_13_12_9_8_1_2595 25 126
  177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 126 177 3 8 42 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 126 177
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 126 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 126 177 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 126 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 126 177 3 7 42 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 126 177 (Polychromatic418967fa.accept_12_8_6_9_1_1608
  20 126 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 126 177
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 126 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 126 177 3 6 42 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 126 177 (Polychromatic418967fa.accept_11_6_5_1_1_586 17 126 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 126 177 (Polychromatic418967fa.accept_12_4_6_9_1_548 16 126
  177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 126 177 3 5 42 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 126 177
  (Polychromatic418967fa.accept_12_2_6_9_1_19 14 126 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 126 177 (Polychromatic418967fa.accept_10_3_6_7_1_2188 13 126 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 126 177 3 4 42 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 126 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 11
  126 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 126 177
  (Polychromatic418967fa.accept_12_10_6_9_1_549 10 126 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 126 177 3 3 42 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 126 177 (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 126 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 126 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 126 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 126 177 3 2 42 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 126 177
  (Polychromatic418967fa.accept_15_5_6_12_1_916 5 126 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 126 177 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 126 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 126 177 3 1 42 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 126 177 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 126 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 126 177
  (Polychromatic418967fa.accept_10_1_6_7_1_710 1 126 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 126 177)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 125 177 (Eq.refl Bool.true)
  (allA_succ_of_accept 52 125 177 (accept_3_4 52 125 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 125 177 (Polychromatic418967fa.accept_12_3_5_9_1_176 51 125 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 125 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 125 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 125 177 (accept_3_4 49 125 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 125 177 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 125 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 125 177
  (Polychromatic418967fa.accept_9_2_8_6_1_79 47 125 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 125 177 (accept_3_4 46 125 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 125 177 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 125 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 125 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 125 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 125 177 (accept_3_4 43 125 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 125 177 (Polychromatic418967fa.accept_10_2_5_7_1_1124 42 125 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 125 177
  (Polychromatic418967fa.accept_9_5_8_6_1_281 41 125 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 125 177 (accept_3_4 40 125 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 125 177 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 125 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 125 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 125 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 125 177 (accept_3_4 37 125 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 125 177 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 125 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 125 177
  (Polychromatic418967fa.accept_16_3_13_1_1_1206 35 125 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 125 177 (accept_3_4 34 125 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 125 177 (Polychromatic418967fa.accept_10_3_5_7_1_330 33 125 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 125 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 125 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 125 177 (accept_3_4 31 125 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 125 177 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 125 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 125 177
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 125 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 125 177 (accept_3_4 28 125 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 125 177 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 125 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 125 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 125 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 125 177 (accept_3_4 25 125 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 125 177 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 125 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 125 177
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 125 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 125 177 (accept_3_4 22 125 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 125 177 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 125 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 125 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 125 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 125 177 (accept_3_4 19 125 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 125 177 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 125 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 125 177
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 125 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 125 177 (accept_3_4 16 125 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 125 177 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 125 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 125 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 125 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 125 177 (accept_3_4 13 125 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 125 177 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 125 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 125 177
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 125 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 125 177 (accept_3_4 10 125 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  125 177 (Polychromatic418967fa.accept_15_9_5_12_1_1640 9 125 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 125 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 125 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 125 177 (accept_3_4 7 125 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 125 177 (Polychromatic418967fa.accept_15_6_5_12_1_1642 6 125 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 125 177
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 125 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 125 177 (accept_3_4 4 125 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  125 177 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 125 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 125 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 125 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 125 177 (accept_3_4 1 125 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 125 177))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 124 177
  (Eq.refl Bool.true) (allA_succ_of_accept 53 124 177 (accept_3_5 53 124 177 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 124 177 (Polychromatic418967fa.accept_7_3_5_2_1_17 52 124 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 124 177 (Polychromatic418967fa.accept_10_1_4_7_1_374 51 124
  177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 124 177 (accept_3_5 50 124
  177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 124 177
  (Polychromatic418967fa.accept_6_1_4_3_1_14 49 124 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 124 177 (Polychromatic418967fa.accept_9_3_7_6_1_76 48 124 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 124 177 (accept_3_5 47 124 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 124 177 (Polychromatic418967fa.accept_7_4_5_2_1_243 46 124 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 124 177 (Polychromatic418967fa.accept_7_3_5_2_1_17 45
  124 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 124 177 (accept_3_5 44
  124 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 124 177
  (Polychromatic418967fa.accept_6_1_4_3_1_14 43 124 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 124 177 (Polychromatic418967fa.accept_10_2_4_7_1_352 42 124 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 124 177 (accept_3_5 41 124 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 124 177 (Polychromatic418967fa.accept_9_4_7_6_1_255 40 124 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 124 177 (Polychromatic418967fa.accept_7_4_5_2_1_243
  39 124 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 124 177 (accept_3_5 38
  124 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 124 177
  (Polychromatic418967fa.accept_6_1_4_3_1_14 37 124 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 124 177 (Polychromatic418967fa.accept_13_10_7_8_1_1794 36 124 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 124 177 (accept_3_5 35 124 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 124 177 (Polychromatic418967fa.accept_16_2_12_1_1_3086 34 124 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 124 177
  (Polychromatic418967fa.accept_10_3_4_7_1_353 33 124 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 124 177 (accept_3_5 32 124 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 124 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 124 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 124 177 (Polychromatic418967fa.accept_9_3_7_6_1_76 30 124 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 124 177 (accept_3_5 29 124 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 124 177 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 124 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 124 177
  (Polychromatic418967fa.accept_13_1_7_8_1_1796 27 124 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 124 177 (accept_3_5 26 124 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 124 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 124 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 124 177 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 124 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 124 177 (accept_3_5 23 124 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 124 177 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 124 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 124 177
  (Polychromatic418967fa.accept_8_5_4_1_1_111 21 124 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 124 177 (accept_3_5 20 124 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 124 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 124 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 124 177 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 124 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 124 177 (accept_3_5 17 124 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 124 177 (Polychromatic418967fa.accept_13_3_7_8_1_4192 16 124 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 124 177
  (Polychromatic418967fa.accept_13_2_7_8_1_4221 15 124 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 124 177 (accept_3_5 14 124 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 124 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 124 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 124 177 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 124 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 124 177 (accept_3_5 11 124 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 124 177 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 124 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 124 177
  (Polychromatic418967fa.accept_13_9_7_8_1_1122 9 124 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 124 177 (accept_3_5 8 124 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  124 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 124 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 124 177 (Polychromatic418967fa.accept_12_6_4_9_1_544 6 124 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 124 177 (accept_3_5 5 124 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 124 177 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 124 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 124 177
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 124 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 124 177 (accept_3_5 2 124 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  124 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 124 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 124 177)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 123 177 (Eq.refl
  Bool.true) (allA_succ_of_gcd 54 123 177 3 18 41 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 123 177 (Polychromatic418967fa.accept_12_5_3_9_1_541 53 123 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 123 177
  (Polychromatic418967fa.accept_15_7_3_12_1_365 52 123 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 123 177 3 17 41 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 123 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 123 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 123 177 (Polychromatic418967fa.accept_12_1_3_9_1_174
  49 123 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 123 177 3 16 41 59
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 123 177
  (Polychromatic418967fa.accept_7_5_4_2_1_235 47 123 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 123 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 123 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 123 177 3 15 41 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 123 177 (Polychromatic418967fa.accept_10_4_3_7_1_1110
  44 123 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 123 177
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 43 123 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 123 177 3 14 41 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 123 177 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 123 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 123 177 (Polychromatic418967fa.accept_7_5_4_2_1_235
  40 123 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 123 177 3 13 41 59
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 123 177
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 123 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 123 177 (Polychromatic418967fa.accept_12_1_3_9_1_174 37 123 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 123 177 3 12 41 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 123 177 (Polychromatic418967fa.accept_10_5_3_7_1_1108
  35 123 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 123 177
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 123 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 123 177 3 11 41 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 123 177 (Polychromatic418967fa.accept_11_10_2_1_1_1036 32 123 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 177
  (Polychromatic418967fa.accept_12_7_3_9_1_999 31 123 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 123 177 3 10 41 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 123 177 (Polychromatic418967fa.accept_12_5_3_9_1_541 29 123 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 123 177 (Polychromatic418967fa.accept_13_2_6_8_1_1092
  28 123 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 123 177 3 9 41 59
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 123 177
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 123 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 123 177 (Polychromatic418967fa.accept_10_5_3_7_1_1108 25 123 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 123 177 3 8 41 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 123 177 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  23 123 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 123 177
  (Polychromatic418967fa.accept_4_2_3_1_1_2 22 123 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 123 177 3 7 41 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 123 177 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 123 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 177 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 123 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 123 177 3 6 41 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 123 177
  (Polychromatic418967fa.accept_12_5_3_9_1_541 17 123 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 123 177 (Polychromatic418967fa.accept_10_6_3_7_1_2197 16 123 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 123 177 3 5 41 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 123 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 14
  123 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 177
  (Polychromatic418967fa.accept_7_6_4_2_1_236 13 123 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 123 177 3 4 41 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 123 177 (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 123 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 123 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 123 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 123 177 3 3 41 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 123 177
  (Polychromatic418967fa.accept_15_8_3_12_1_1657 8 123 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 123 177 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 123 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 123 177 3 2 41 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 123 177 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 123 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 177
  (Polychromatic418967fa.accept_10_4_3_7_1_1110 4 123 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 123 177 3 1 41 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 123 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 123 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 177 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 123 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 123
  177))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 122 177 (Eq.refl Bool.true)
  (allA_succ_of_accept 55 122 177 (accept_3_4 55 122 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 122 177 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 122 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 122 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 122 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 122 177 (accept_3_4 52 122 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 122 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 122 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 122 177
  (Polychromatic418967fa.accept_7_1_3_2_1_13 50 122 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 122 177 (accept_3_4 49 122 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 122 177 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 122 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 122 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 122 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 122 177 (accept_3_4 46 122 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 122 177 (Polychromatic418967fa.accept_10_5_2_7_1_345 45 122 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 122 177
  (Polychromatic418967fa.accept_9_8_5_6_1_538 44 122 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 122 177 (accept_3_4 43 122 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 122 177 (Polychromatic418967fa.accept_12_6_2_9_1_537 42 122 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 122 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 122 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 122 177 (accept_3_4 40 122 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 122 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 122 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 122 177
  (Polychromatic418967fa.accept_9_2_5_6_1_536 38 122 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 122 177 (accept_3_4 37 122 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 122 177 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 122 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 122 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 122 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 122 177 (accept_3_4 34 122 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 122 177 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 122 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 122 177
  (Polychromatic418967fa.accept_19_13_8_6_1_7195 32 122 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 122 177 (accept_3_4 31 122 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 122 177 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 122 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 122 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 122 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 122 177 (accept_3_4 28 122 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 122 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 122 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 122 177
  (Polychromatic418967fa.accept_7_5_3_2_1_249 26 122 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 122 177 (accept_3_4 25 122 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 122 177 (Polychromatic418967fa.accept_10_4_2_7_1_373 24 122 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 122 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 122 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 122 177 (accept_3_4 22 122 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 122 177 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 122 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 122 177
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 122 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 122 177 (accept_3_4 19 122 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 122 177 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 122 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 122 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 122 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 122 177 (accept_3_4 16 122 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 122 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 122 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 122 177
  (Polychromatic418967fa.accept_10_4_2_7_1_373 14 122 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 122 177 (accept_3_4 13 122 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 122 177 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 122 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 122 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 122 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 122 177 (accept_3_4 10 122 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 122 177 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 122 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 122 177
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 122 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 122 177 (accept_3_4 7 122 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  122 177 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 122 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 122 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 122 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 122 177 (accept_3_4 4 122 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 122 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 122 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 122 177
  (Polychromatic418967fa.accept_9_2_5_6_1_536 2 122 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 122 177 (accept_3_4 1 122 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  177)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 121 177 (Eq.refl Bool.true)
  (allA_succ_of_accept 56 121 177 (accept_3_5 56 121 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 121 177 (Polychromatic418967fa.accept_9_1_4_6_1_5 55 121 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 121 177 (Polychromatic418967fa.accept_10_4_1_7_1_371 54 121 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 121 177 (accept_3_5 53 121 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 121 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 121 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 121 177
  (Polychromatic418967fa.accept_12_3_1_9_1_202 51 121 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 121 177 (accept_3_5 50 121 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 121 177 (Polychromatic418967fa.accept_13_10_4_8_1_2570 49 121 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 121 177 (Polychromatic418967fa.accept_9_3_4_6_1_252 48 121 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 121 177 (accept_3_5 47 121 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 121 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 121 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 121 177
  (Polychromatic418967fa.accept_16_13_9_1_1_3022 45 121 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 121 177 (accept_3_5 44 121 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 121 177 (Polychromatic418967fa.accept_9_7_4_6_1_273 43 121 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 121 177 (Polychromatic418967fa.accept_16_10_9_1_1_9973 42 121 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 121 177 (accept_3_5 41 121 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 121 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 121 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 121 177
  (Polychromatic418967fa.accept_9_3_4_6_1_252 39 121 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 121 177 (accept_3_5 38 121 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 121 177 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 121 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 121 177 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 121 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 121 177 (accept_3_5 35 121 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 121 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 121 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 121 177
  (Polychromatic418967fa.accept_19_14_7_6_1_8654 33 121 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 121 177 (accept_3_5 32 121 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 121 177 (Polychromatic418967fa.accept_20_11_1_17_1_5535 31 121 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 121 177 (Polychromatic418967fa.accept_9_3_4_6_1_252 30 121 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 121 177 (accept_3_5 29 121 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 121 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 121 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 121 177
  (Polychromatic418967fa.accept_12_3_1_9_1_202 27 121 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 121 177 (accept_3_5 26 121 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 121 177 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 121 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 121 177 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 121 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 121 177 (accept_3_5 23 121 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 121 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 121 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 121 177
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 121 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 121 177 (accept_3_5 20 121 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 121 177 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 121 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 121 177 (Polychromatic418967fa.accept_16_2_9_1_1_6404 18 121 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 121 177 (accept_3_5 17 121 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 121 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 121 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 121 177
  (Polychromatic418967fa.accept_12_3_1_9_1_202 15 121 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 121 177 (accept_3_5 14 121 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 121 177 (Polychromatic418967fa.accept_15_13_1_12_1_1638 13 121 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 121 177 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 121 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 121 177 (accept_3_5 11 121 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 121 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 121 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 121 177
  (Polychromatic418967fa.accept_13_9_4_8_1_1752 9 121 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 121 177 (accept_3_5 8 121 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  121 177 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 121 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 121 177 (Polychromatic418967fa.accept_10_6_1_7_1_342 6 121 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 121 177 (accept_3_5 5 121 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 121 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 121 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 121 177
  (Polychromatic418967fa.accept_9_3_4_6_1_252 3 121 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 121 177 (accept_3_5 2 121 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  121 177 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 121 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 121 177))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 120 177 (Eq.refl
  Bool.true) (allA_succ_of_gcd 57 120 177 3 19 40 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 56 120 177 (Polychromatic418967fa.accept_9_2_3_6_1_88 56 120 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 120 177
  (Polychromatic418967fa.accept_7_6_1_2_1_230 55 120 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 120 177 3 18 40 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 120 177 (Polychromatic418967fa.accept_9_8_3_6_1_533 53 120 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 120 177 (Polychromatic418967fa.accept_7_3_1_2_1_247
  52 120 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 120 177 3 17 40 59
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 120 177
  (Polychromatic418967fa.accept_9_5_3_6_1_269 50 120 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 120 177 (Polychromatic418967fa.accept_9_4_3_6_1_532 49 120 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 120 177 3 16 40 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 120 177 (Polychromatic418967fa.accept_9_2_3_6_1_88 47
  120 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 120 177
  (Polychromatic418967fa.accept_9_1_3_6_1_70 46 120 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 120 177 3 15 40 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 120 177 (Polychromatic418967fa.accept_9_8_3_6_1_533 44 120 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 120 177 (Polychromatic418967fa.accept_9_7_3_6_1_270
  43 120 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 120 177 3 14 40 59
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 120 177
  (Polychromatic418967fa.accept_7_6_1_2_1_230 41 120 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 120 177 (Polychromatic418967fa.accept_9_4_3_6_1_532 40 120 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 120 177 3 13 40 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 120 177 (Polychromatic418967fa.accept_7_3_1_2_1_247 38
  120 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 120 177
  (Polychromatic418967fa.accept_9_1_3_6_1_70 37 120 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 120 177 3 12 40 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 120 177 (Polychromatic418967fa.accept_9_8_3_6_1_533 35 120 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 120 177 (Polychromatic418967fa.accept_7_6_1_2_1_230
  34 120 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 120 177 3 11 40 59
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 120 177
  (Polychromatic418967fa.accept_9_5_3_6_1_269 32 120 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 120 177 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 120 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 120 177 3 10 40 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 120 177 (Polychromatic418967fa.accept_9_2_3_6_1_88 29
  120 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 120 177
  (Polychromatic418967fa.accept_9_1_3_6_1_70 28 120 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 120 177 3 9 40 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 120 177 (Polychromatic418967fa.accept_9_8_3_6_1_533 26 120 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 120 177 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 120 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 120 177 3 8 40 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 120 177
  (Polychromatic418967fa.accept_9_5_3_6_1_269 23 120 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 120 177 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 120 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 120 177 3 7 40 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 120 177 (Polychromatic418967fa.accept_7_6_1_2_1_230 20
  120 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 120 177
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 120 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 120 177 3 6 40 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 120 177 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 120 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 120 177 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 120 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 120 177 3 5 40 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 120 177
  (Polychromatic418967fa.accept_9_5_3_6_1_269 14 120 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 120 177 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 120 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 177 3 4 40 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 177 (Polychromatic418967fa.accept_9_2_3_6_1_88 11
  120 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 120 177
  (Polychromatic418967fa.accept_7_3_1_2_1_247 10 120 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 120 177 3 3 40 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 120 177 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 120 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 120 177 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 120 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120 177 3 2 40 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 120 177
  (Polychromatic418967fa.accept_9_5_3_6_1_269 5 120 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 120 177 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 120 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 120 177 3 1 40 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 120 177 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 120 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 120 177
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 120 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 120 177)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 119 177 (Eq.refl Bool.true)
  (allA_succ_of_accept 58 119 177 (accept_3_4 58 119 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 119 177 (Polychromatic418967fa.accept_9_3_2_6_1_264 57 119 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 119 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 119 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 119 177 (accept_3_4 55 119 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 119 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 119 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 119 177
  (Polychromatic418967fa.accept_9_8_2_6_1_875 53 119 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 119 177 (accept_3_4 52 119 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 119 177 (Polychromatic418967fa.accept_12_3_11_9_1_193 51 119 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 119 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 119 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 119 177 (accept_3_4 49 119 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 119 177 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 119 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 119 177
  (Polychromatic418967fa.accept_14_5_7_9_1_3828 47 119 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 119 177 (accept_3_4 46 119 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 119 177 (Polychromatic418967fa.accept_13_6_2_8_1_1782 45 119 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 119 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 119 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 119 177 (accept_3_4 43 119 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 119 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 119 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 119 177
  (Polychromatic418967fa.accept_9_5_2_6_1_265 41 119 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 119 177 (accept_3_4 40 119 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 119 177 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 119 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 119 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 119 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 119 177 (accept_3_4 37 119 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 119 177 (Polychromatic418967fa.accept_13_10_2_8_1_2603 36 119 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 119 177
  (Polychromatic418967fa.accept_9_8_2_6_1_875 35 119 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 119 177 (accept_3_4 34 119 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 119 177 (Polychromatic418967fa.accept_13_7_2_8_1_1746 33 119 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 119 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 119 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 119 177 (accept_3_4 31 119 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 119 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 119 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 119 177
  (Polychromatic418967fa.accept_32_29_23_17_1_9990 29 119 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 119 177 (accept_3_4 28 119 177 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 119 177 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 119 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 119 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 119 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 119 177 (accept_3_4 25 119 177
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 119 177
  (Polychromatic418967fa.accept_15_9_14_12_1_913 24 119 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 119 177 (Polychromatic418967fa.accept_9_5_2_6_1_265 23 119 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 119 177 (accept_3_4 22 119 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 119 177 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 119 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 119 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 20
  119 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 119 177 (accept_3_4 19
  119 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 119 177
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 119 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 119 177 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 119 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 119 177 (accept_3_4 16 119 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 119 177 (Polychromatic418967fa.accept_12_3_11_9_1_193 15 119 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 119 177
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 119 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 119 177 (accept_3_4 13 119 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 119 177 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 119 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 119 177 (Polychromatic418967fa.accept_15_11_14_12_1_2458 11 119 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 177 (accept_3_4 10 119 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 119 177 (Polychromatic418967fa.accept_15_9_14_12_1_913 9 119
  177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 177
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 119 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 119 177 (accept_3_4 7 119 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  119 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 119 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 119 177 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 119 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 177 (accept_3_4 4 119 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 119 177 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 119 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 177
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 119 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 119 177 (accept_3_4 1 119 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  177))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 118 177 (Eq.refl Bool.true)
  (allA_succ_of_gcd 59 118 177 59 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 58 118 177 (Polychromatic418967fa.accept_9_4_1_6_1_284 58 118 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 118 177 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 118 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 118 177 (accept_3_5 56 118 177
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 118 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 55
  118 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 118 177
  (Polychromatic418967fa.accept_12_6_10_9_1_531 54 118 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 118 177 (accept_3_5 53 118 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 118 177 (Polychromatic418967fa.accept_7_3_6_2_1_90 52 118 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 118 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 118 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 118 177 (accept_3_5 50 118 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 118 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 118 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 118 177
  (Polychromatic418967fa.accept_9_3_1_6_1_86 48 118 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 118 177 (accept_3_5 47 118 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 118 177 (Polychromatic418967fa.accept_7_4_6_2_1_451 46 118 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 118 177 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 118 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 118 177 (accept_3_5 44 118 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 118 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 118 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 118 177
  (Polychromatic418967fa.accept_12_6_10_9_1_531 42 118 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 118 177 (accept_3_5 41 118 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 118 177 (Polychromatic418967fa.accept_9_4_1_6_1_284 40 118 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 118 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 118 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 118 177 (accept_3_5 38 118 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 118 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 118 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 118 177
  (Polychromatic418967fa.accept_7_1_6_2_1_18 36 118 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 118 177 (accept_3_5 35 118 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 118 177 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 118 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 118 177 (Polychromatic418967fa.accept_13_7_1_8_1_1778 33 118 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 118 177 (accept_3_5 32 118 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 118 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 118 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 118 177
  (Polychromatic418967fa.accept_9_3_1_6_1_86 30 118 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 118 177 (accept_3_5 29 118 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 118 177 (Polychromatic418967fa.accept_21_7_13_9_1_6937 28 118 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 118 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 118 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 118 177 (accept_3_5 26 118 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 118 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 118 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 118 177
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 118 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 118 177 (accept_3_5 23 118 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 118 177 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 118 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 118 177 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 118 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 118 177 (accept_3_5 20 118 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 118 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 118 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 118 177
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 118 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 118 177 (accept_3_5 17 118 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 118 177 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 118 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 118 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 118 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 118 177 (accept_3_5 14 118 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 118 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 118 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 118 177
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 118 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 118 177 (accept_3_5 11 118 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 118 177 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 118 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 118 177 (Polychromatic418967fa.accept_10_9_8_7_1_714 9 118 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 118 177 (accept_3_5 8 118 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 118 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 118 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 118 177
  (Polychromatic418967fa.accept_12_6_10_9_1_531 6 118 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 118 177 (accept_3_5 5 118 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  118 177 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 118 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 118 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 118 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 118 177 (accept_3_5 2 118 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 118 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 118 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118
  177)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 117 177 (Eq.refl Bool.true)
  (allA_succ_of_gcd 60 117 177 3 20 39 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 117 177 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 117 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 117 177
  (Polychromatic418967fa.accept_18_4_9_15_1_3383 58 117 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 117 177 3 19 39 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 117 177 (Polychromatic418967fa.accept_17_5_15_7_1_4992 56 117 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 117 177
  (Polychromatic418967fa.accept_19_17_3_6_1_8662 55 117 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 117 177 3 18 39 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 117 177 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 117 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 117 177 (Polychromatic418967fa.accept_7_3_5_2_1_17 52
  117 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 117 177 3 17 39 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 117 177
  (Polychromatic418967fa.accept_11_6_7_1_1_564 50 117 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 117 177 (Polychromatic418967fa.accept_14_7_5_9_1_2911 49 117 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 117 177 3 16 39 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 117 177 (Polychromatic418967fa.accept_16_15_5_1_1_7724
  47 117 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 117 177
  (Polychromatic418967fa.accept_7_4_5_2_1_243 46 117 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 117 177 3 15 39 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 117 177 (Polychromatic418967fa.accept_8_4_5_1_1_299 44 117 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 177
  (Polychromatic418967fa.accept_17_9_15_7_1_6212 43 117 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 117 177 3 14 39 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 117 177 (Polychromatic418967fa.accept_16_9_5_1_1_1259 41 117 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 117 177
  (Polychromatic418967fa.accept_18_4_9_15_1_3383 40 117 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 117 177 3 13 39 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 117 177 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 117 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 177
  (Polychromatic418967fa.accept_19_18_3_6_1_9989 37 117 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 117 177 3 12 39 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 117 177 (Polychromatic418967fa.accept_14_7_5_9_1_2911 35 117 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 177
  (Polychromatic418967fa.accept_18_16_9_15_1_4614 34 117 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 33 117 177 3 11 39 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 32 117 177 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 117 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 177
  (Polychromatic418967fa.accept_7_3_5_2_1_17 31 117 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 117 177 3 10 39 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 117 177 (Polychromatic418967fa.accept_16_13_5_1_1_3017 29 117 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 177
  (Polychromatic418967fa.accept_8_4_5_1_1_299 28 117 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 117 177 3 9 39 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 117 177 (Polychromatic418967fa.accept_17_9_15_7_1_6212 26 117 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 177 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 117 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 117 177 3 8 39 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 117 177
  (Polychromatic418967fa.accept_18_5_9_15_1_4695 23 117 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 117 177 (Polychromatic418967fa.accept_16_6_5_1_1_7761 22 117 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 117 177 3 7 39 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 117 177 (Polychromatic418967fa.accept_8_4_5_1_1_299 20
  117 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 177
  (Polychromatic418967fa.accept_17_2_15_7_1_6213 19 117 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 117 177 3 6 39 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 117 177 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 117 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 177 (Polychromatic418967fa.accept_18_16_9_15_1_4614 16 117
  177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 117 177 3 5 39 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 117 177
  (Polychromatic418967fa.accept_23_14_2_16_1_9988 14 117 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 117 177 (Polychromatic418967fa.accept_16_13_5_1_1_3017 13 117 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 117 177 3 4 39 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 117 177
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 117 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 117 177 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 117 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 117 177 3 3 39 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 117 177 (Polychromatic418967fa.accept_19_8_3_6_1_9982 8 117 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 177
  (Polychromatic418967fa.accept_14_7_5_9_1_2911 7 117 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 117 177 3 2 39 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 117 177 (Polychromatic418967fa.accept_17_5_15_7_1_4992 5 117 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 177 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 117 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 117 177 3 1 39 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 117 177
  (Polychromatic418967fa.accept_17_2_15_7_1_6213 2 117 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 117 177 (Polychromatic418967fa.accept_19_1_3_6_1_5827 1 117 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 117 177)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 62 116 177 (Eq.refl Bool.true) (allA_succ_of_accept 61 116 177 (accept_3_4 61 116 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 116 177 (Polychromatic418967fa.accept_11_5_6_1_1_988 60 116 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 116 177
  (Polychromatic418967fa.accept_6_5_2_3_1_81 59 116 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 116 177 (accept_3_4 58 116 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 116 177 (Polychromatic418967fa.accept_9_3_8_6_1_80 57 116 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 116 177 (Polychromatic418967fa.accept_9_2_8_6_1_79 56 116 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 116 177 (accept_3_4 55 116 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 116 177 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 116 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 116 177
  (Polychromatic418967fa.accept_6_5_2_3_1_81 53 116 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 116 177 (accept_3_4 52 116 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 116 177 (Polychromatic418967fa.accept_10_1_6_7_1_710 51 116 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 116 177 (Polychromatic418967fa.accept_9_5_8_6_1_281 50 116 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 116 177 (accept_3_4 49 116 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 116 177 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 116 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 116 177
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 116 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 116 177 (accept_3_4 46 116 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 116 177 (Polychromatic418967fa.accept_8_5_4_1_1_111 45 116 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 116 177 (Polychromatic418967fa.accept_13_5_12_8_1_198 44 116 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 116 177 (accept_3_4 43 116 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 116 177 (Polychromatic418967fa.accept_12_6_8_9_1_553 42 116
  177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 116 177
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 116 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 116 177 (accept_3_4 40 116 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 116 177 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 116 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 116 177 (Polychromatic418967fa.accept_9_2_8_6_1_79 38 116 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 116 177 (accept_3_4 37 116 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 116 177 (Polychromatic418967fa.accept_13_10_12_8_1_2550 36 116 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 116 177
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 116 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 116 177 (accept_3_4 34 116 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 116 177 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 116 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 116 177 (Polychromatic418967fa.accept_9_5_8_6_1_281 32 116 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 116 177 (accept_3_4 31 116 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 116 177 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 116 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 116 177
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 116 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 116 177 (accept_3_4 28 116 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 116 177 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 116 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 116 177 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 116 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 116 177 (accept_3_4 25 116 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 116 177 (Polychromatic418967fa.accept_16_8_4_1_1_2102 24 116 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 116 177
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 116 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 116 177 (accept_3_4 22 116 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 116 177 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 116 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 116 177 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 116 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 116 177 (accept_3_4 19 116 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 116 177 (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 116 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 116 177
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 116 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 116 177 (accept_3_4 16 116 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 116 177 (Polychromatic418967fa.accept_19_15_2_6_1_7179 15 116 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 116 177 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 116 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 116 177 (accept_3_4 13 116 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 116 177 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 116 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 116 177
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 116 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 116 177 (accept_3_4 10 116 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  116 177 (Polychromatic418967fa.accept_13_9_12_8_1_570 9 116 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 116 177 (Polychromatic418967fa.accept_15_8_11_12_1_1626 8 116 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 116 177 (accept_3_4 7 116 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 116 177 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 116 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 116 177
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 116 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 116 177 (accept_3_4 4 116 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  116 177 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 116 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 116 177 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 116 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 116 177 (accept_3_4 1 116 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 116 177)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63
  115 177 (Eq.refl Bool.true) (allA_succ_of_accept 62 115 177 (accept_3_5 62 115 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 115 177 (Polychromatic418967fa.accept_7_5_3_2_1_249 61 115 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 115 177 (Polychromatic418967fa.accept_19_3_1_6_1_3114
  60 115 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 115 177 (accept_3_5 59
  115 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 115 177
  (Polychromatic418967fa.accept_4_2_3_1_1_2 58 115 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 115 177 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 115 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 115 177 (accept_3_5 56 115 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 115 177 (Polychromatic418967fa.accept_7_6_3_2_1_461 55 115 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 115 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 54
  115 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 115 177 (accept_3_5 53
  115 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 115 177
  (Polychromatic418967fa.accept_6_4_1_3_1_77 52 115 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 115 177 (Polychromatic418967fa.accept_12_3_7_9_1_1009 51 115 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 115 177 (accept_3_5 50 115 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 115 177 (Polychromatic418967fa.accept_9_4_7_6_1_255 49 115 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 115 177 (Polychromatic418967fa.accept_7_6_3_2_1_461
  48 115 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 115 177 (accept_3_5 47
  115 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 115 177
  (Polychromatic418967fa.accept_4_2_3_1_1_2 46 115 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 115 177 (Polychromatic418967fa.accept_13_6_11_8_1_1111 45 115 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 115 177 (accept_3_5 44 115 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 115 177 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 115 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 115 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 42
  115 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 115 177 (accept_3_5 41
  115 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 115 177
  (Polychromatic418967fa.accept_6_4_1_3_1_77 40 115 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 115 177 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 115 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 115 177 (accept_3_5 38 115 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 115 177 (Polychromatic418967fa.accept_9_1_7_6_1_75 37 115 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 115 177 (Polychromatic418967fa.accept_7_1_3_2_1_13 36
  115 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 115 177 (accept_3_5 35
  115 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 115 177
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 115 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 115 177 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 115 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 115 177 (accept_3_5 32 115 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 115 177 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 115 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 115 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 30
  115 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 115 177 (accept_3_5 29
  115 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 115 177
  (Polychromatic418967fa.accept_6_4_1_3_1_77 28 115 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 115 177 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 115 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 115 177 (accept_3_5 26 115 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 115 177 (Polychromatic418967fa.accept_20_5_15_17_1_7077 25 115 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 115 177
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 24 115 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 115 177 (accept_3_5 23 115 177 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 115 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 115 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 115 177 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 115 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 115 177 (accept_3_5 20 115 177
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 115 177 (Polychromatic418967fa.accept_7_5_3_2_1_249
  19 115 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 115 177
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 115 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 115 177 (accept_3_5 17 115 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 115 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 115 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 115 177 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 115 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 115 177 (accept_3_5 14 115 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 115 177 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 115 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 115 177
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 115 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 115 177 (accept_3_5 11 115 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 115 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 115 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 115 177 (Polychromatic418967fa.accept_13_9_11_8_1_195 9 115 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 115 177 (accept_3_5 8 115 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 115 177 (Polychromatic418967fa.accept_15_7_10_12_1_2403 7 115 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 115 177
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 115 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 115 177 (accept_3_5 5 115 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  115 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 115 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 115 177 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 115 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 177 (accept_3_5 2 115 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 115 177 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 115 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115
  177))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 114 177 (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 114 177 3 21 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 114 177 (Polychromatic418967fa.accept_10_2_4_7_1_352 62 114 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 114 177 (Polychromatic418967fa.accept_10_1_4_7_1_374
  61 114 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 114 177 3 20 38 59
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 114 177
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 114 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 114 177 (Polychromatic418967fa.accept_12_10_6_9_1_549 58 114 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 114 177 3 19 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 114 177 (Polychromatic418967fa.accept_12_8_6_9_1_1608
  56 114 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 114 177
  (Polychromatic418967fa.accept_4_3_2_1_1_50 55 114 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 114 177 3 18 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 114 177 (Polychromatic418967fa.accept_10_3_4_7_1_353 53 114 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 114 177 (Polychromatic418967fa.accept_10_2_4_7_1_352
  52 114 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 114 177 3 17 38 59
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 114 177
  (Polychromatic418967fa.accept_12_2_6_9_1_19 50 114 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 114 177 (Polychromatic418967fa.accept_14_7_2_9_1_2093 49 114 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 114 177 3 16 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 114 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 47
  114 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 114 177
  (Polychromatic418967fa.accept_12_10_6_9_1_549 46 114 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 114 177 3 15 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 114 177 (Polychromatic418967fa.accept_12_8_6_9_1_1608 44 114 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 114 177
  (Polychromatic418967fa.accept_4_3_2_1_1_50 43 114 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 114 177 3 14 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 114 177 (Polychromatic418967fa.accept_10_1_4_7_1_374 41 114 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 114 177 (Polychromatic418967fa.accept_12_4_6_9_1_548
  40 114 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 114 177 3 13 38 59
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 114 177
  (Polychromatic418967fa.accept_12_2_6_9_1_19 38 114 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 114 177 (Polychromatic418967fa.accept_13_11_10_8_1_1804 37 114 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 114 177 3 12 38 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 114 177
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 114 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 114 177 (Polychromatic418967fa.accept_12_10_6_9_1_549 34 114 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 114 177 3 11 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 114 177 (Polychromatic418967fa.accept_10_2_4_7_1_352
  32 114 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 114 177
  (Polychromatic418967fa.accept_4_3_2_1_1_50 31 114 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 114 177 3 10 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 114 177 (Polychromatic418967fa.accept_15_14_9_12_1_2498 29 114 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 114 177
  (Polychromatic418967fa.accept_12_4_6_9_1_548 28 114 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 114 177 3 9 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 114 177 (Polychromatic418967fa.accept_12_2_6_9_1_19 26 114 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 114 177 (Polychromatic418967fa.accept_13_12_10_8_1_3343 25 114
  177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 114 177 3 8 38 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 114 177
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 114 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 114 177 (Polychromatic418967fa.accept_10_2_4_7_1_352 22 114 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 114 177 3 7 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 114 177 (Polychromatic418967fa.accept_12_8_6_9_1_1608
  20 114 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 114 177
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 114 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 177 3 6 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 114 177 (Polychromatic418967fa.accept_13_4_10_8_1_1817 17 114 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 114 177 (Polychromatic418967fa.accept_12_4_6_9_1_548 16 114
  177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 114 177 3 5 38 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 114 177
  (Polychromatic418967fa.accept_12_2_6_9_1_19 14 114 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 114 177 (Polychromatic418967fa.accept_10_3_4_7_1_353 13 114 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 114 177 3 4 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 114 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 11
  114 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 114 177
  (Polychromatic418967fa.accept_12_10_6_9_1_549 10 114 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 114 177 3 3 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 114 177 (Polychromatic418967fa.accept_11_8_4_1_1_1000 8 114 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 114 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 114 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114 177 3 2 38 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 114 177
  (Polychromatic418967fa.accept_13_5_10_8_1_1127 5 114 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 114 177 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 114 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 114 177 3 1 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 114 177 (Polychromatic418967fa.accept_10_2_4_7_1_352 2 114 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 114 177
  (Polychromatic418967fa.accept_10_1_4_7_1_374 1 114 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 114 177)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 113 177 (Eq.refl
  Bool.true) (allA_succ_of_accept 64 113 177 (accept_3_4 64 113 177 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 113 177 (Polychromatic418967fa.accept_12_3_5_9_1_176 63 113 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 113 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 113 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 113 177 (accept_3_4 61 113 177
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 113 177
  (Polychromatic418967fa.accept_18_6_5_15_1_7292 60 113 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 113 177 (Polychromatic418967fa.accept_7_3_1_2_1_247 59 113 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 113 177 (accept_3_4 58 113 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 113 177 (Polychromatic418967fa.accept_9_3_5_6_1_253 57 113 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 113 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 56
  113 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 113 177 (accept_3_4 55
  113 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 113 177
  (Polychromatic418967fa.accept_10_4_3_7_1_1110 54 113 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 113 177 (Polychromatic418967fa.accept_9_8_5_6_1_538 53 113 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 113 177 (accept_3_4 52 113 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 113 177 (Polychromatic418967fa.accept_12_3_5_9_1_176 51 113 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 113 177
  (Polychromatic418967fa.accept_6_2_5_3_1_16 50 113 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 113 177 (accept_3_4 49 113 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 113 177 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 113 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 113 177 (Polychromatic418967fa.accept_9_2_5_6_1_536 47 113 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 113 177 (accept_3_4 46 113 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 113 177 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 113 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 113 177
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 113 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 113 177 (accept_3_4 43 113 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 113 177 (Polychromatic418967fa.accept_13_3_9_8_1_4202 42 113 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 113 177 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 113 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 113 177 (accept_3_4 40 113 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 113 177 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 113 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 113 177
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 113 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 113 177 (accept_3_4 37 113 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 113 177 (Polychromatic418967fa.accept_10_6_3_7_1_2197 36 113 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 113 177 (Polychromatic418967fa.accept_9_8_5_6_1_538 35 113 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 113 177 (accept_3_4 34 113 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 113 177 (Polychromatic418967fa.accept_13_7_9_8_1_188 33 113 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 113 177
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 113 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 113 177 (accept_3_4 31 113 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 113 177 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 113 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 113 177 (Polychromatic418967fa.accept_9_2_5_6_1_536 29 113 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 113 177 (accept_3_4 28 113 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 113 177 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 113 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 113 177
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 113 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 113 177 (accept_3_4 25 113 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 113 177 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 113 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 113 177 (Polychromatic418967fa.accept_25_23_13_2_1_8183 23 113 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 113 177 (accept_3_4 22 113 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 113 177 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 113 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 177
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 113 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 113 177 (accept_3_4 19 113 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 113 177 (Polychromatic418967fa.accept_15_3_8_12_1_900 18 113 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 113 177 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 113 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 177 (accept_3_4 16 113 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 113 177 (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 113 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 177
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 113 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 113 177 (accept_3_4 13 113 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 113 177 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 113 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 113 177 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 113 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 177 (accept_3_4 10 113 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 177 (Polychromatic418967fa.accept_18_9_5_15_1_2246 9 113 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 177
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 113 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 113 177 (accept_3_4 7 113 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  113 177 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 113 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 113 177 (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 113 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 177 (accept_3_4 4 113 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 177 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 113 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 177
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 113 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 177 (accept_3_4 1 113 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  177))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 112 177 (Eq.refl Bool.true)
  (allA_succ_of_accept 65 112 177 (accept_3_5 65 112 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 112 177 (Polychromatic418967fa.accept_9_1_4_6_1_5 64 112 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 112 177 (Polychromatic418967fa.accept_15_3_7_12_1_372 63 112 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 112 177 (accept_3_5 62 112 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 112 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 112 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 112 177
  (Polychromatic418967fa.accept_18_6_4_15_1_2276 60 112 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 112 177 (accept_3_5 59 112 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 112 177 (Polychromatic418967fa.accept_11_3_2_1_1_994 58 112 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 112 177 (Polychromatic418967fa.accept_9_3_4_6_1_252 57 112 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 112 177 (accept_3_5 56 112 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 112 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 112 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 112 177
  (Polychromatic418967fa.accept_10_4_2_7_1_373 54 112 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 112 177 (accept_3_5 53 112 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 112 177 (Polychromatic418967fa.accept_9_7_4_6_1_273 52 112 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 112 177 (Polychromatic418967fa.accept_15_6_7_12_1_869 51 112 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 112 177 (accept_3_5 50 112 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 112 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 112 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 112 177
  (Polychromatic418967fa.accept_9_3_4_6_1_252 48 112 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 112 177 (accept_3_5 47 112 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 112 177 (Polychromatic418967fa.accept_9_1_4_6_1_5 46 112 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 112 177 (Polychromatic418967fa.accept_10_5_2_7_1_345 45 112 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 112 177 (accept_3_5 44 112 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 112 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 112 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 112 177
  (Polychromatic418967fa.accept_12_6_4_9_1_544 42 112 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 112 177 (accept_3_5 41 112 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 112 177 (Polychromatic418967fa.accept_15_10_7_12_1_2490 40 112 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 112 177 (Polychromatic418967fa.accept_9_3_4_6_1_252 39 112 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 112 177 (accept_3_5 38 112 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 112 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 112 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 112 177
  (Polychromatic418967fa.accept_11_3_2_1_1_994 36 112 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 112 177 (accept_3_5 35 112 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 112 177 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 112 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 112 177 (Polychromatic418967fa.accept_15_3_7_12_1_372 33 112 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 112 177 (accept_3_5 32 112 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 112 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 112 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 112 177
  (Polychromatic418967fa.accept_9_3_4_6_1_252 30 112 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 112 177 (accept_3_5 29 112 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 112 177 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 112 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 112 177 (Polychromatic418967fa.accept_18_9_4_15_1_555 27 112 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 112 177 (accept_3_5 26 112 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 112 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 112 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 112 177
  (Polychromatic418967fa.accept_10_4_2_7_1_373 24 112 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 112 177 (accept_3_5 23 112 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 112 177 (Polychromatic418967fa.accept_19_3_17_6_1_1991 22 112 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 112 177 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 112 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 112 177 (accept_3_5 20 112 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 112 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 112 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 112 177
  (Polychromatic418967fa.accept_12_6_4_9_1_544 18 112 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 112 177 (accept_3_5 17 112 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 112 177 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 112 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 112 177 (Polychromatic418967fa.accept_10_5_2_7_1_345 15 112 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 112 177 (accept_3_5 14 112 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 112 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 112 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 112 177
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 112 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 112 177 (accept_3_5 11 112 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 112 177 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 112 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 112 177 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 112 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 112 177 (accept_3_5 8 112 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 112 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 112 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 112 177
  (Polychromatic418967fa.accept_12_6_4_9_1_544 6 112 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 112 177 (accept_3_5 5 112 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  112 177 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 112 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 112 177 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 112 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 112 177 (accept_3_5 2 112 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 112 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 112 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112
  177)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 111 177 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 111 177 3 22 37 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 111 177 (Polychromatic418967fa.accept_9_2_3_6_1_88 65 111 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 111 177 (Polychromatic418967fa.accept_7_1_6_2_1_18 64
  111 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 111 177 3 21 37 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 111 177
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 111 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 111 177 (Polychromatic418967fa.accept_9_7_3_6_1_270 61 111 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 111 177 3 20 37 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 111 177 (Polychromatic418967fa.accept_7_3_6_2_1_90 59
  111 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 111 177
  (Polychromatic418967fa.accept_4_2_3_1_1_2 58 111 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 111 177 3 19 37 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 111 177 (Polychromatic418967fa.accept_9_2_3_6_1_88 56 111 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 177 (Polychromatic418967fa.accept_9_1_3_6_1_70 55
  111 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 111 177 3 18 37 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 111 177
  (Polychromatic418967fa.accept_7_4_6_2_1_451 53 111 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 111 177 (Polychromatic418967fa.accept_7_3_6_2_1_90 52 111 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 111 177 3 17 37 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 111 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 50
  111 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 177
  (Polychromatic418967fa.accept_9_4_3_6_1_532 49 111 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 111 177 3 16 37 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 111 177 (Polychromatic418967fa.accept_9_2_3_6_1_88 47 111 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 111 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 46
  111 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 111 177 3 15 37 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 111 177
  (Polychromatic418967fa.accept_9_8_3_6_1_533 44 111 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 111 177 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 111 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 111 177 3 14 37 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 111 177 (Polychromatic418967fa.accept_9_5_3_6_1_269 41
  111 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 111 177
  (Polychromatic418967fa.accept_9_4_3_6_1_532 40 111 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 111 177 3 13 37 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 111 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 111 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 177 (Polychromatic418967fa.accept_9_1_3_6_1_70 37
  111 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 111 177 3 12 37 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 111 177
  (Polychromatic418967fa.accept_9_8_3_6_1_533 35 111 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 111 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 111 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 111 177 3 11 37 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 111 177 (Polychromatic418967fa.accept_7_4_6_2_1_451 32
  111 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 177
  (Polychromatic418967fa.accept_7_3_6_2_1_90 31 111 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 111 177 3 10 37 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 111 177 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 111 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 177 (Polychromatic418967fa.accept_9_1_3_6_1_70 28
  111 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 111 177 3 9 37 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 111 177
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 111 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 111 177 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 111 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 111 177 3 8 37 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 111 177 (Polychromatic418967fa.accept_9_5_3_6_1_269 23
  111 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 111 177
  (Polychromatic418967fa.accept_4_2_3_1_1_2 22 111 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 111 177 3 7 37 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 111 177 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 111 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 177 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 111 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 111 177 3 6 37 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 111 177
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 111 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 111 177 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 111 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 111 177 3 5 37 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 111 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 14
  111 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 177
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 111 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 111 177 3 4 37 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 111 177 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 111 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 111 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 111 177 3 3 37 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 111 177
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 111 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 111 177 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 111 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 111 177 3 2 37 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 111 177 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 111 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 177
  (Polychromatic418967fa.accept_7_4_6_2_1_451 4 111 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 111 177 3 1 37 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 111 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 111 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 177 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 111 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111
  177))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 110 177 (Eq.refl Bool.true)
  (allA_succ_of_accept 67 110 177 (accept_3_4 67 110 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 110 177 (Polychromatic418967fa.accept_7_3_5_2_1_17 66 110 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 110 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 110 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 110 177 (accept_3_4 64 110 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 110 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 110 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 110 177
  (Polychromatic418967fa.accept_9_8_2_6_1_875 62 110 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 110 177 (accept_3_4 61 110 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 110 177 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 110 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 110 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 110 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 110 177 (accept_3_4 58 110 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 110 177 (Polychromatic418967fa.accept_9_3_2_6_1_264 57 110 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 110 177
  (Polychromatic418967fa.accept_21_14_5_9_1_8526 56 110 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 110 177 (accept_3_4 55 110 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 110 177 (Polychromatic418967fa.accept_12_6_2_9_1_537 54 110 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 110 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 110 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 110 177 (accept_3_4 52 110 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 110 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 110 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 110 177
  (Polychromatic418967fa.accept_9_5_2_6_1_265 50 110 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 110 177 (accept_3_4 49 110 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 110 177 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 110 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 110 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 110 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 110 177 (accept_3_4 46 110 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 110 177 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 110 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 110 177
  (Polychromatic418967fa.accept_9_8_2_6_1_875 44 110 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 110 177 (accept_3_4 43 110 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 110 177 (Polychromatic418967fa.accept_12_6_2_9_1_537 42 110 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 110 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 110 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 110 177 (accept_3_4 40 110 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 110 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 110 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 110 177
  (Polychromatic418967fa.accept_7_3_5_2_1_17 38 110 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 110 177 (accept_3_4 37 110 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 110 177 (Polychromatic418967fa.accept_15_6_5_12_1_1642 36 110 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 110 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 110 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 110 177 (accept_3_4 34 110 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 110 177 (Polychromatic418967fa.accept_17_16_8_7_1_4983 33 110 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 110 177
  (Polychromatic418967fa.accept_7_4_5_2_1_243 32 110 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 110 177 (accept_3_4 31 110 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 110 177 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 110 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 110 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 110 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 110 177 (accept_3_4 28 110 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 110 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 110 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 110 177
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 110 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 110 177 (accept_3_4 25 110 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 110 177 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 110 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 110 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 110 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 110 177 (accept_3_4 22 110 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 110 177 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 110 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 110 177
  (Polychromatic418967fa.accept_16_4_14_1_1_1241 20 110 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 110 177 (accept_3_4 19 110 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 110 177 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 110 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 110 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 110 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 110 177 (accept_3_4 16 110 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 110 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 110 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 110 177
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 110 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 110 177 (accept_3_4 13 110 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 110 177 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 110 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 110 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 110 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 110 177 (accept_3_4 10 110 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 110 177 (Polychromatic418967fa.accept_15_9_5_12_1_1640 9 110 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 110 177
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 110 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 110 177 (accept_3_4 7 110 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  110 177 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 110 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 110 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 110 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 110 177 (accept_3_4 4 110 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 110 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 110 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 110 177
  (Polychromatic418967fa.accept_13_2_6_8_1_1092 2 110 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 110 177 (accept_3_4 1 110 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  177)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 109 177 (Eq.refl Bool.true)
  (allA_succ_of_accept 68 109 177 (accept_3_5 68 109 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 109 177 (Polychromatic418967fa.accept_9_4_1_6_1_284 67 109 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 109 177 (Polychromatic418967fa.accept_9_3_1_6_1_86 66 109 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 109 177 (accept_3_5 65 109 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 109 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 109 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 109 177
  (Polychromatic418967fa.accept_12_3_1_9_1_202 63 109 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 109 177 (accept_3_5 62 109 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 109 177 (Polychromatic418967fa.accept_7_5_4_2_1_235 61 109 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 109 177 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 109 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 109 177 (accept_3_5 59 109 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 109 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 109 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 109 177
  (Polychromatic418967fa.accept_9_3_1_6_1_86 57 109 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 109 177 (accept_3_5 56 109 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 109 177 (Polychromatic418967fa.accept_7_6_4_2_1_236 55 109 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 109 177 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 109 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 109 177 (accept_3_5 53 109 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 109 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 109 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 109 177
  (Polychromatic418967fa.accept_12_3_1_9_1_202 51 109 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 109 177 (accept_3_5 50 109 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 109 177 (Polychromatic418967fa.accept_9_4_1_6_1_284 49 109 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 109 177 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 109 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 109 177 (accept_3_5 47 109 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 109 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 109 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 109 177
  (Polychromatic418967fa.accept_19_7_14_6_1_9987 45 109 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 109 177 (accept_3_5 44 109 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 109 177 (Polychromatic418967fa.accept_9_7_1_6_1_261 43 109 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 109 177 (Polychromatic418967fa.accept_10_2_9_7_1_720 42 109 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 109 177 (accept_3_5 41 109 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 109 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 109 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 109 177
  (Polychromatic418967fa.accept_9_3_1_6_1_86 39 109 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 109 177 (accept_3_5 38 109 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 109 177 (Polychromatic418967fa.accept_15_7_4_12_1_2530 37 109 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 109 177 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 109 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 109 177 (accept_3_5 35 109 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 109 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 109 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 109 177
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 109 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 109 177 (accept_3_5 32 109 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 109 177 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 109 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 109 177 (Polychromatic418967fa.accept_9_3_1_6_1_86 30 109 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 109 177 (accept_3_5 29 109 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 109 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 109 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 109 177
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 109 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 109 177 (accept_3_5 26 109 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 109 177 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 109 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 109 177 (Polychromatic418967fa.accept_11_2_10_1_1_1017 24 109 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 109 177 (accept_3_5 23 109 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 109 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 109 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 109 177
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 109 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 109 177 (accept_3_5 20 109 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 109 177 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 109 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 109 177 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 109 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 109 177 (accept_3_5 17 109 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 109 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 109 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 109 177
  (Polychromatic418967fa.accept_12_3_1_9_1_202 15 109 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 109 177 (accept_3_5 14 109 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 109 177 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 109 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 109 177 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 109 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 109 177 (accept_3_5 11 109 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 109 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 109 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 109 177
  (Polychromatic418967fa.accept_11_9_10_1_1_581 9 109 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 109 177 (accept_3_5 8 109 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  109 177 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 109 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 109 177 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 109 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 109 177 (accept_3_5 5 109 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 109 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 109 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 109 177
  (Polychromatic418967fa.accept_9_3_1_6_1_86 3 109 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 109 177 (accept_3_5 2 109 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  109 177 (Polychromatic418967fa.accept_13_1_5_8_1_207 1 109 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 109 177))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 108
  177 (Eq.refl Bool.true) (allA_succ_of_gcd 69 108 177 3 23 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 108 177 (Polychromatic418967fa.accept_7_5_3_2_1_249 68 108 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 108 177
  (Polychromatic418967fa.accept_15_7_3_12_1_365 67 108 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 108 177 3 22 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 108 177 (Polychromatic418967fa.accept_10_5_8_7_1_2174 65 108 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 108 177
  (Polychromatic418967fa.accept_7_1_3_2_1_13 64 108 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 108 177 3 21 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 108 177 (Polychromatic418967fa.accept_7_6_3_2_1_461 62 108 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 108 177 (Polychromatic418967fa.accept_7_5_3_2_1_249
  61 108 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 108 177 3 20 36 59
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 108 177
  (Polychromatic418967fa.accept_10_9_8_7_1_714 59 108 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 108 177 (Polychromatic418967fa.accept_15_13_3_12_1_1609 58 108 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 108 177 3 19 36 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 108 177
  (Polychromatic418967fa.accept_16_8_12_1_1_7720 56 108 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 108 177 (Polychromatic418967fa.accept_7_6_3_2_1_461 55 108 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 108 177 3 18 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 108 177 (Polychromatic418967fa.accept_8_5_4_1_1_111 53
  108 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 108 177
  (Polychromatic418967fa.accept_15_7_3_12_1_365 52 108 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 108 177 3 17 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 108 177 (Polychromatic418967fa.accept_7_1_3_2_1_13 50 108 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 108 177 (Polychromatic418967fa.accept_10_9_8_7_1_714
  49 108 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 108 177 3 16 36 59
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 108 177
  (Polychromatic418967fa.accept_7_5_3_2_1_249 47 108 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 108 177 (Polychromatic418967fa.accept_19_8_13_6_1_7153 46 108 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 108 177 3 15 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 108 177 (Polychromatic418967fa.accept_21_2_3_9_1_1317
  44 108 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 108 177
  (Polychromatic418967fa.accept_7_1_3_2_1_13 43 108 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 108 177 3 14 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 108 177 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 108 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 108 177 (Polychromatic418967fa.accept_7_5_3_2_1_249
  40 108 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 108 177 3 13 36 59
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 108 177
  (Polychromatic418967fa.accept_13_12_4_8_1_1120 38 108 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 108 177 (Polychromatic418967fa.accept_8_5_4_1_1_111 37 108 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 108 177 3 12 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 108 177 (Polychromatic418967fa.accept_10_5_8_7_1_2174
  35 108 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 108 177
  (Polychromatic418967fa.accept_7_6_3_2_1_461 34 108 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 108 177 3 11 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 108 177 (Polychromatic418967fa.accept_11_10_9_1_1_2186 32 108 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 108 177
  (Polychromatic418967fa.accept_17_14_6_7_1_4980 31 108 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 108 177 3 10 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 108 177 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 108 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 108 177
  (Polychromatic418967fa.accept_15_13_3_12_1_1609 28 108 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 108 177 3 9 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 108 177 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 108 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 108 177
  (Polychromatic418967fa.accept_10_5_8_7_1_2174 25 108 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 108 177 3 8 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 108 177 (Polychromatic418967fa.accept_13_10_4_8_1_2570 23 108 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 108 177 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 108 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 108 177 3 7 36 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 108 177
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 108 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 108 177 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 108 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 108 177 3 6 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 108 177 (Polychromatic418967fa.accept_15_2_3_12_1_891
  17 108 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 108 177
  (Polychromatic418967fa.accept_17_16_6_7_1_2715 16 108 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 108 177 3 5 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 108 177 (Polychromatic418967fa.accept_17_14_6_7_1_4980 14 108 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 108 177 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 108 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 108 177 3 4 36 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 108 177
  (Polychromatic418967fa.accept_13_11_4_8_1_1098 11 108 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 108 177 (Polychromatic418967fa.accept_11_10_9_1_1_2186 10 108 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 108 177 3 3 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 108 177 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 108 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 108 177
  (Polychromatic418967fa.accept_15_7_3_12_1_365 7 108 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 108 177 3 2 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 108 177 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 108 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 108 177 (Polychromatic418967fa.accept_16_4_12_1_1_1204 4 108
  177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 108 177 3 1 36 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 108 177
  (Polychromatic418967fa.accept_15_2_3_12_1_891 2 108 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 108 177 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 108 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 108
  177)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 107 177 (Eq.refl Bool.true)
  (allA_succ_of_accept 70 107 177 (accept_3_4 70 107 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 107 177 (Polychromatic418967fa.accept_20_9_7_17_1_1655 69 107 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 107 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 107 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 107 177 (accept_3_4 67 107 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 107 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 107 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 107 177
  (Polychromatic418967fa.accept_9_2_8_6_1_79 65 107 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 107 177 (accept_3_4 64 107 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 107 177 (Polychromatic418967fa.accept_12_3_11_9_1_193 63 107 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 107 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 107 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 107 177 (accept_3_4 61 107 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 107 177 (Polychromatic418967fa.accept_16_12_11_1_1_4088 60 107 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 107 177
  (Polychromatic418967fa.accept_9_5_8_6_1_281 59 107 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 107 177 (accept_3_4 58 107 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 107 177 (Polychromatic418967fa.accept_9_3_8_6_1_80 57 107 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 107 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 107 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 107 177 (accept_3_4 55 107 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 107 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 107 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 107 177
  (Polychromatic418967fa.accept_19_15_12_6_1_8634 53 107 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 107 177 (accept_3_4 52 107 177 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 107 177 (Polychromatic418967fa.accept_12_3_11_9_1_193 51 107 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 107 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 107 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 107 177 (accept_3_4 49 107 177
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 107 177 (Polychromatic418967fa.accept_9_3_8_6_1_80 48
  107 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 107 177
  (Polychromatic418967fa.accept_9_2_8_6_1_79 47 107 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 107 177 (accept_3_4 46 107 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 107 177 (Polychromatic418967fa.accept_17_11_5_7_1_6177 45 107 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 107 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 107 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 107 177 (accept_3_4 43 107 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 107 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 107 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 107 177
  (Polychromatic418967fa.accept_9_5_8_6_1_281 41 107 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 107 177 (accept_3_4 40 107 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 107 177 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 107 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 107 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 107 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 107 177 (accept_3_4 37 107 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 107 177 (Polychromatic418967fa.accept_15_6_2_12_1_885 36 107 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 107 177
  (Polychromatic418967fa.accept_13_9_3_8_1_573 35 107 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 107 177 (accept_3_4 34 107 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 107 177 (Polychromatic418967fa.accept_13_7_3_8_1_1750 33 107 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 107 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 107 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 107 177 (accept_3_4 31 107 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 107 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 107 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 107 177
  (Polychromatic418967fa.accept_9_2_8_6_1_79 29 107 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 107 177 (accept_3_4 28 107 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 107 177 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 107 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 107 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 107 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 107 177 (accept_3_4 25 107 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 107 177 (Polychromatic418967fa.accept_13_11_3_8_1_1786 24 107 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 107 177
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 107 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 107 177 (accept_3_4 22 107 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 107 177 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 107 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 107 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 107 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 107 177 (accept_3_4 19 107 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 107 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 107 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 107 177
  (Polychromatic418967fa.accept_19_17_12_6_1_8650 17 107 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 107 177 (accept_3_4 16 107 177 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 107 177 (Polychromatic418967fa.accept_11_4_8_1_1_1047 15 107 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 107 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 107 177 (accept_3_4 13 107 177
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 107 177 (Polychromatic418967fa.accept_9_3_8_6_1_80 12
  107 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 107 177
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 107 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 107 177 (accept_3_4 10 107 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  107 177 (Polychromatic418967fa.accept_13_9_3_8_1_573 9 107 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 107 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 107 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 107 177 (accept_3_4 7 107 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 107 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 107 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 107 177
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 107 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 107 177 (accept_3_4 4 107 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  107 177 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 107 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 107 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 107 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 107 177 (accept_3_4 1 107 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 107 177)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 72 106 177 (Eq.refl Bool.true) (allA_succ_of_accept 71 106 177 (accept_3_5 71 106 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 106 177 (Polychromatic418967fa.accept_19_13_11_6_1_3128 70 106 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 106 177
  (Polychromatic418967fa.accept_7_6_1_2_1_230 69 106 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 106 177 (accept_3_5 68 106 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 106 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 106 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 106 177 (Polychromatic418967fa.accept_7_3_1_2_1_247 66 106 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 106 177 (accept_3_5 65 106 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 106 177 (Polychromatic418967fa.accept_9_1_7_6_1_75 64 106 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 106 177
  (Polychromatic418967fa.accept_4_3_2_1_1_50 63 106 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 106 177 (accept_3_5 62 106 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 106 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 106 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 106 177 (Polychromatic418967fa.accept_18_6_16_15_1_7287 60 106 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 106 177 (accept_3_5 59 106 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 106 177 (Polychromatic418967fa.accept_9_4_7_6_1_255 58 106 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 106 177
  (Polychromatic418967fa.accept_9_3_7_6_1_76 57 106 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 106 177 (accept_3_5 56 106 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 106 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 106 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 106 177 (Polychromatic418967fa.accept_12_6_10_9_1_531 54 106 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 106 177 (accept_3_5 53 106 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 106 177 (Polychromatic418967fa.accept_7_3_1_2_1_247 52 106 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 106 177
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 106 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 106 177 (accept_3_5 50 106 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 106 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 106 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 106 177 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 106 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 106 177 (accept_3_5 47 106 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 106 177 (Polychromatic418967fa.accept_9_1_7_6_1_75 46 106 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 106 177
  (Polychromatic418967fa.accept_7_3_1_2_1_247 45 106 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 106 177 (accept_3_5 44 106 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 106 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 106 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 106 177 (Polychromatic418967fa.accept_12_6_10_9_1_531 42 106 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 106 177 (accept_3_5 41 106 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 106 177 (Polychromatic418967fa.accept_9_4_7_6_1_255 40 106 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 106 177
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 106 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 106 177 (accept_3_5 38 106 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 106 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 106 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 106 177 (Polychromatic418967fa.accept_13_10_2_8_1_2603 36 106 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 106 177 (accept_3_5 35 106 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 106 177 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 106 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 106 177
  (Polychromatic418967fa.accept_10_3_6_7_1_2188 33 106 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 106 177 (accept_3_5 32 106 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 106 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 106 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 106 177 (Polychromatic418967fa.accept_9_3_7_6_1_76 30 106 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 106 177 (accept_3_5 29 106 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 106 177 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 106 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 106 177
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 106 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 106 177 (accept_3_5 26 106 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 106 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 106 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 106 177 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 106 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 106 177 (accept_3_5 23 106 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 106 177 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 106 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 106 177
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 106 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 106 177 (accept_3_5 20 106 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 106 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 106 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 106 177 (Polychromatic418967fa.accept_12_6_10_9_1_531 18 106 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 106 177 (accept_3_5 17 106 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 106 177 (Polychromatic418967fa.accept_19_16_11_6_1_7149 16 106
  177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 106 177
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 106 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 106 177 (accept_3_5 14 106 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 106 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 106 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 106 177 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 106 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 106 177 (accept_3_5 11 106 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 106 177 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 106 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 106 177
  (Polychromatic418967fa.accept_16_9_10_1_1_2998 9 106 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 106 177 (accept_3_5 8 106 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  106 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 106 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 106 177 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 106 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 106 177 (accept_3_5 5 106 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 106 177 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 106 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 106 177
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 106 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 106 177 (accept_3_5 2 106 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  106 177 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 106 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 106 177)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73
  105 177 (Eq.refl Bool.true) (allA_succ_of_gcd 72 105 177 3 24 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 105 177 (Polychromatic418967fa.accept_11_5_6_1_1_988 71 105 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 105 177
  (Polychromatic418967fa.accept_13_5_1_8_1_1115 70 105 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 105 177 3 23 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 105 177 (Polychromatic418967fa.accept_10_8_5_7_1_358 68 105 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 105 177
  (Polychromatic418967fa.accept_17_16_3_7_1_5028 67 105 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 105 177 3 22 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 105 177 (Polychromatic418967fa.accept_22_21_17_1_1_9986 65 105 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 105 177
  (Polychromatic418967fa.accept_13_12_1_8_1_1779 64 105 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 105 177 3 21 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 105 177 (Polychromatic418967fa.accept_10_2_5_7_1_1124 62 105 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 177
  (Polychromatic418967fa.accept_13_9_1_8_1_1742 61 105 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 105 177 3 20 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 105 177 (Polychromatic418967fa.accept_13_7_1_8_1_1778 59 105 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 105 177
  (Polychromatic418967fa.accept_10_8_5_7_1_358 58 105 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 105 177 3 19 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 105 177 (Polychromatic418967fa.accept_16_8_9_1_1_7753 56 105 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 105 177
  (Polychromatic418967fa.accept_17_4_3_7_1_4971 55 105 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 105 177 3 18 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 105 177 (Polychromatic418967fa.accept_10_3_5_7_1_330 53 105 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 105 177 (Polychromatic418967fa.accept_10_2_5_7_1_1124
  52 105 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 105 177 3 17 35 59
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 105 177
  (Polychromatic418967fa.accept_13_11_1_8_1_1776 50 105 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 105 177 (Polychromatic418967fa.accept_11_5_6_1_1_988 49 105 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 105 177 3 16 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 105 177 (Polychromatic418967fa.accept_14_5_7_9_1_3828
  47 105 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 105 177
  (Polychromatic418967fa.accept_13_7_1_8_1_1778 46 105 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 105 177 3 15 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 105 177 (Polychromatic418967fa.accept_13_5_1_8_1_1115 44 105 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 177
  (Polychromatic418967fa.accept_10_3_5_7_1_330 43 105 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 105 177 3 14 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 105 177 (Polychromatic418967fa.accept_23_18_13_16_1_9985 41 105 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 105 177
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 40 105 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 105 177 3 13 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 105 177 (Polychromatic418967fa.accept_10_8_5_7_1_358 38 105 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 177
  (Polychromatic418967fa.accept_13_11_1_8_1_1776 37 105 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 105 177 3 12 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 105 177 (Polychromatic418967fa.accept_13_9_1_8_1_1742 35 105 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 105 177
  (Polychromatic418967fa.accept_16_2_9_1_1_6404 34 105 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 105 177 3 11 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 105 177 (Polychromatic418967fa.accept_10_2_5_7_1_1124 32 105 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 177
  (Polychromatic418967fa.accept_13_5_1_8_1_1115 31 105 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 105 177 3 10 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 105 177 (Polychromatic418967fa.accept_11_7_6_1_1_2182 29 105 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 177
  (Polychromatic418967fa.accept_10_8_5_7_1_358 28 105 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 105 177 3 9 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 105 177 (Polychromatic418967fa.accept_14_12_7_9_1_726 26 105 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 177 (Polychromatic418967fa.accept_13_12_1_8_1_1779 25 105
  177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 105 177 3 8 35 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 105 177
  (Polychromatic418967fa.accept_10_3_5_7_1_330 23 105 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 105 177 (Polychromatic418967fa.accept_10_2_5_7_1_1124 22 105 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 105 177 3 7 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 105 177 (Polychromatic418967fa.accept_13_7_1_8_1_1778
  20 105 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 177
  (Polychromatic418967fa.accept_13_6_1_8_1_1116 19 105 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 105 177 3 6 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 105 177 (Polychromatic418967fa.accept_27_17_24_15_1_9984 17 105 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 177 (Polychromatic418967fa.accept_11_5_6_1_1_988
  16 105 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 105 177 3 5 35 59
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 105 177
  (Polychromatic418967fa.accept_19_14_10_6_1_4372 14 105 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 105 177 (Polychromatic418967fa.accept_10_3_5_7_1_330 13 105 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 105 177 3 4 35 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 105 177
  (Polychromatic418967fa.accept_13_11_1_8_1_1776 11 105 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 105 177 (Polychromatic418967fa.accept_16_10_9_1_1_9973 10 105 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 105 177 3 3 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 105 177 (Polychromatic418967fa.accept_10_8_5_7_1_358 8 105 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 177
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 7 105 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 105 177 3 2 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 105 177 (Polychromatic418967fa.accept_11_5_6_1_1_988 5 105 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 177 (Polychromatic418967fa.accept_17_4_3_7_1_4971 4 105 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 105 177 3 1 35 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 105 177
  (Polychromatic418967fa.accept_10_2_5_7_1_1124 2 105 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 105 177 (Polychromatic418967fa.accept_19_1_10_6_1_5726 1 105 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 105
  177))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 104 177 (Eq.refl
  Bool.true) (allA_succ_of_accept 73 104 177 (accept_3_4 73 104 177 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 104 177 (Polychromatic418967fa.accept_10_2_4_7_1_352 72 104 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 104 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 104 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 104 177 (accept_3_4 70 104 177
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 104 177
  (Polychromatic418967fa.accept_15_9_14_12_1_913 69 104 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 104 177 (Polychromatic418967fa.accept_16_4_8_1_1_5257 68 104 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 104 177 (accept_3_4 67 104 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 104 177 (Polychromatic418967fa.accept_7_3_6_2_1_90 66 104 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 104 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 65
  104 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 104 177 (accept_3_4 64
  104 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 104 177
  (Polychromatic418967fa.accept_10_3_4_7_1_353 63 104 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 104 177 (Polychromatic418967fa.accept_9_8_5_6_1_538 62 104 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 104 177 (accept_3_4 61 104 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 104 177 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 104 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 104 177 (Polychromatic418967fa.accept_6_5_2_3_1_81 59
  104 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 104 177 (accept_3_4 58
  104 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 104 177
  (Polychromatic418967fa.accept_7_1_6_2_1_18 57 104 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 104 177 (Polychromatic418967fa.accept_9_2_5_6_1_536 56 104 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 104 177 (accept_3_4 55 104 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 104 177 (Polychromatic418967fa.accept_12_6_8_9_1_553 54 104 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 104 177
  (Polychromatic418967fa.accept_6_5_2_3_1_81 53 104 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 104 177 (accept_3_4 52 104 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 104 177 (Polychromatic418967fa.accept_10_1_4_7_1_374 51 104 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 104 177 (Polychromatic418967fa.accept_7_1_6_2_1_18 50 104 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 104 177 (accept_3_4 49 104 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 104 177 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 104 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 104 177
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 104 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 104 177 (accept_3_4 46 104 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 104 177 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 104 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 104 177 (Polychromatic418967fa.accept_9_8_5_6_1_538 44 104 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 104 177 (accept_3_4 43 104 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 104 177 (Polychromatic418967fa.accept_10_2_4_7_1_352 42 104 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 104 177
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 104 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 104 177 (accept_3_4 40 104 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 104 177 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 104 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 104 177 (Polychromatic418967fa.accept_7_3_6_2_1_90 38 104 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 104 177 (accept_3_4 37 104 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 104 177 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 104 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 104 177
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 104 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 104 177 (accept_3_4 34 104 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 104 177 (Polychromatic418967fa.accept_10_3_4_7_1_353 33 104 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 104 177 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 104 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 104 177 (accept_3_4 31 104 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 104 177 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 104 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 104 177
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 104 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 104 177 (accept_3_4 28 104 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 104 177 (Polychromatic418967fa.accept_20_7_4_17_1_4132 27 104 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 104 177 (Polychromatic418967fa.accept_9_8_5_6_1_538 26 104 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 104 177 (accept_3_4 25 104 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 104 177 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 104 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 104 177
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 104 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 104 177 (accept_3_4 22 104 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 104 177 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 104 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 104 177 (Polychromatic418967fa.accept_9_2_5_6_1_536 20 104 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 104 177 (accept_3_4 19 104 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 104 177 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 104 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 104 177
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 104 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 104 177 (accept_3_4 16 104 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 104 177 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 104 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 104 177 (Polychromatic418967fa.accept_19_14_9_6_1_8633 14 104 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 104 177 (accept_3_4 13 104 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 104 177 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 104 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 104 177
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 104 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 104 177 (accept_3_4 10 104 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  104 177 (Polychromatic418967fa.accept_15_9_14_12_1_913 9 104 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 104 177 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 104 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 104 177 (accept_3_4 7 104 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 104 177 (Polychromatic418967fa.accept_11_6_5_1_1_586 6 104 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 104 177
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 104 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 104 177 (accept_3_4 4 104 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  104 177 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 104 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 104 177 (Polychromatic418967fa.accept_9_2_5_6_1_536 2 104 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 104 177 (accept_3_4 1 104 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 104 177))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 75 103 177 (Eq.refl Bool.true) (allA_succ_of_accept 74 103 177 (accept_3_5 74 103 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 103 177 (Polychromatic418967fa.accept_7_3_5_2_1_17 73 103 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 103 177
  (Polychromatic418967fa.accept_13_7_12_8_1_199 72 103 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 103 177 (accept_3_5 71 103 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 103 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 103 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 103 177 (Polychromatic418967fa.accept_13_4_12_8_1_197 69 103 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 103 177 (accept_3_5 68 103 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 103 177 (Polychromatic418967fa.accept_7_4_5_2_1_243 67 103 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 103 177
  (Polychromatic418967fa.accept_4_2_3_1_1_2 66 103 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 103 177 (accept_3_5 65 103 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 103 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 103 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 103 177 (Polychromatic418967fa.accept_11_8_4_1_1_1000 63 103 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 103 177 (accept_3_5 62 103 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 103 177 (Polychromatic418967fa.accept_9_7_4_6_1_273 61 103 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 103 177
  (Polychromatic418967fa.accept_7_4_5_2_1_243 60 103 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 103 177 (accept_3_5 59 103 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 103 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 103 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 103 177 (Polychromatic418967fa.accept_9_3_4_6_1_252 57 103 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 103 177 (accept_3_5 56 103 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 103 177 (Polychromatic418967fa.accept_9_1_4_6_1_5 55 103 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 103 177
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 103 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 103 177 (accept_3_5 53 103 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 103 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 103 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 103 177 (Polychromatic418967fa.accept_12_3_7_9_1_1009 51 103 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 103 177 (accept_3_5 50 103 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 103 177 (Polychromatic418967fa.accept_13_10_12_8_1_2550 49 103
  177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 103 177
  (Polychromatic418967fa.accept_9_3_4_6_1_252 48 103 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 103 177 (accept_3_5 47 103 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 103 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 103 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 103 177 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 103 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 103 177 (accept_3_5 44 103 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 103 177 (Polychromatic418967fa.accept_9_7_4_6_1_273 43 103 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 103 177
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 103 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 103 177 (accept_3_5 41 103 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 103 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 103 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 103 177 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 103 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 103 177 (accept_3_5 38 103 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 103 177 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 103 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 103 177
  (Polychromatic418967fa.accept_10_6_3_7_1_2197 36 103 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 103 177 (accept_3_5 35 103 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 103 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 103 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 103 177 (Polychromatic418967fa.accept_13_7_12_8_1_199 33 103 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 103 177 (accept_3_5 32 103 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 103 177 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 103 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 103 177
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 103 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 103 177 (accept_3_5 29 103 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 103 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 103 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 103 177 (Polychromatic418967fa.accept_12_3_7_9_1_1009 27 103 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 103 177 (accept_3_5 26 103 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 103 177 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 103 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 103 177
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 103 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 103 177 (accept_3_5 23 103 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 103 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 103 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 103 177 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 103 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 103 177 (accept_3_5 20 103 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 103 177 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 103 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 103 177
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 103 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 103 177 (accept_3_5 17 103 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 103 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 103 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 103 177 (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 103 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 103 177 (accept_3_5 14 103 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 103 177 (Polychromatic418967fa.accept_19_13_8_6_1_7195 13 103
  177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 103 177
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 103 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 103 177 (accept_3_5 11 103 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 103 177 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 103 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 103 177 (Polychromatic418967fa.accept_13_9_12_8_1_570 9 103 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 103 177 (accept_3_5 8 103 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 103 177 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 103 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 103 177
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 103 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 103 177 (accept_3_5 5 103 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  103 177 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 103 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 103 177 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 103 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 103 177 (accept_3_5 2 103 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 103 177 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 103 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 103
  177))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76 102 177 (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 102 177 3 25 34 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 74 102 177 (Polychromatic418967fa.accept_9_2_3_6_1_88 74 102 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 102 177
  (Polychromatic418967fa.accept_9_1_3_6_1_70 73 102 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 102 177 3 24 34 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 102 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 102 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 102 177 (Polychromatic418967fa.accept_9_7_3_6_1_270
  70 102 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 102 177 3 23 34 59
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 102 177
  (Polychromatic418967fa.accept_7_5_4_2_1_235 68 102 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 102 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 102 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 102 177 3 22 34 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 102 177 (Polychromatic418967fa.accept_9_2_3_6_1_88 65
  102 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 102 177
  (Polychromatic418967fa.accept_9_1_3_6_1_70 64 102 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 102 177 3 21 34 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 102 177 (Polychromatic418967fa.accept_7_6_4_2_1_236 62 102 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 102 177 (Polychromatic418967fa.accept_7_5_4_2_1_235
  61 102 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 102 177 3 20 34 59
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 102 177
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 102 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 102 177 (Polychromatic418967fa.accept_9_4_3_6_1_532 58 102 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 102 177 3 19 34 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 102 177 (Polychromatic418967fa.accept_9_2_3_6_1_88 56
  102 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 102 177
  (Polychromatic418967fa.accept_4_3_2_1_1_50 55 102 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 102 177 3 18 34 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 102 177 (Polychromatic418967fa.accept_9_8_3_6_1_533 53 102 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 102 177 (Polychromatic418967fa.accept_9_7_3_6_1_270
  52 102 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 102 177 3 17 34 59
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 102 177
  (Polychromatic418967fa.accept_9_5_3_6_1_269 50 102 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 102 177 (Polychromatic418967fa.accept_9_4_3_6_1_532 49 102 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 102 177 3 16 34 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 102 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 47
  102 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 102 177
  (Polychromatic418967fa.accept_9_1_3_6_1_70 46 102 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 102 177 3 15 34 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 102 177 (Polychromatic418967fa.accept_9_8_3_6_1_533 44 102 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 102 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 43
  102 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 102 177 3 14 34 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 102 177
  (Polychromatic418967fa.accept_7_6_4_2_1_236 41 102 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 102 177 (Polychromatic418967fa.accept_7_5_4_2_1_235 40 102 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 102 177 3 13 34 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 102 177 (Polychromatic418967fa.accept_9_2_3_6_1_88 38
  102 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 102 177
  (Polychromatic418967fa.accept_9_1_3_6_1_70 37 102 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 177 3 12 34 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 102 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 102 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 102 177 (Polychromatic418967fa.accept_7_6_4_2_1_236
  34 102 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 102 177 3 11 34 59
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 102 177
  (Polychromatic418967fa.accept_9_5_3_6_1_269 32 102 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 102 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 102 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 102 177 3 10 34 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 102 177 (Polychromatic418967fa.accept_9_2_3_6_1_88 29
  102 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 102 177
  (Polychromatic418967fa.accept_9_1_3_6_1_70 28 102 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 102 177 3 9 34 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 102 177 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 102 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 102 177 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 102 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 102 177 3 8 34 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 102 177
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 102 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 102 177 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 102 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 102 177 3 7 34 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 102 177 (Polychromatic418967fa.accept_7_6_4_2_1_236 20
  102 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 102 177
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 102 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 177 3 6 34 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 102 177 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 102 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 102 177 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 102 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 102 177 3 5 34 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 102 177
  (Polychromatic418967fa.accept_9_5_3_6_1_269 14 102 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 102 177 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 102 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 102 177 3 4 34 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 102 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 11
  102 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 102 177
  (Polychromatic418967fa.accept_9_1_3_6_1_70 10 102 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 102 177 3 3 34 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 102 177 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 102 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 102 177 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 102 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102 177 3 2 34 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 102 177
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 102 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 102 177 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 102 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 102 177 3 1 34 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 102 177 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 102 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 102 177
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 102 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 102 177)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 101 177
  (Eq.refl Bool.true) (allA_succ_of_accept 76 101 177 (accept_3_4 76 101 177 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 101 177 (Polychromatic418967fa.accept_7_5_3_2_1_249 75 101 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 101 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 74 101 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 101 177 (accept_3_4 73 101 177
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 101 177 (Polychromatic418967fa.accept_13_7_10_8_1_567
  72 101 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 101 177
  (Polychromatic418967fa.accept_7_1_3_2_1_13 71 101 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 101 177 (accept_3_4 70 101 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 101 177 (Polychromatic418967fa.accept_7_6_3_2_1_461 69 101 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 101 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 101 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 101 177 (accept_3_4 67 101 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 101 177 (Polychromatic418967fa.accept_9_3_2_6_1_264 66 101 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 101 177
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 65 101 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 101 177 (accept_3_4 64 101 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 101 177 (Polychromatic418967fa.accept_12_3_5_9_1_176 63 101 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 101 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 101 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 101 177 (accept_3_4 61 101 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 101 177 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 101 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 101 177
  (Polychromatic418967fa.accept_9_5_2_6_1_265 59 101 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 101 177 (accept_3_4 58 101 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 101 177 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 101 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 101 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 101 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 101 177 (accept_3_4 55 101 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 101 177 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 101 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 101 177
  (Polychromatic418967fa.accept_9_8_2_6_1_875 53 101 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 101 177 (accept_3_4 52 101 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 101 177 (Polychromatic418967fa.accept_12_3_5_9_1_176 51 101 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 101 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 101 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 101 177 (accept_3_4 49 101 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 101 177 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 101 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 101 177
  (Polychromatic418967fa.accept_7_5_3_2_1_249 47 101 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 101 177 (accept_3_4 46 101 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 101 177 (Polychromatic418967fa.accept_16_13_5_1_1_3017 45 101 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 101 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 101 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 101 177 (accept_3_4 43 101 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 101 177 (Polychromatic418967fa.accept_17_8_16_7_1_8792 42 101 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 101 177
  (Polychromatic418967fa.accept_7_6_3_2_1_461 41 101 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 101 177 (accept_3_4 40 101 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 101 177 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 101 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 101 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 101 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 101 177 (accept_3_4 37 101 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 101 177 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 101 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 101 177
  (Polychromatic418967fa.accept_9_8_2_6_1_875 35 101 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 101 177 (accept_3_4 34 101 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 101 177 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 101 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 101 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 101 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 101 177 (accept_3_4 31 101 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 101 177 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 101 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 101 177
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 101 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 101 177 (accept_3_4 28 101 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 101 177 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 101 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 101 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 101 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 101 177 (accept_3_4 25 101 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 101 177 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 101 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 101 177
  (Polychromatic418967fa.accept_9_5_2_6_1_265 23 101 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 101 177 (accept_3_4 22 101 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 101 177 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 101 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 101 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 101 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 101 177 (accept_3_4 19 101 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 101 177 (Polychromatic418967fa.accept_13_5_10_8_1_1127 18 101 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 101 177
  (Polychromatic418967fa.accept_9_8_2_6_1_875 17 101 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 101 177 (accept_3_4 16 101 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 101 177 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 101 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 101 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 101 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 101 177 (accept_3_4 13 101 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 101 177 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 101 177 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 101 177
  (Polychromatic418967fa.accept_13_11_10_8_1_1804 11 101 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 101 177 (accept_3_4 10 101 177 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 101 177 (Polychromatic418967fa.accept_16_9_5_1_1_1259 9 101 177 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 101 177
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 101 177 (accept_3_4 7 101 177
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 101 177 (Polychromatic418967fa.accept_7_6_3_2_1_461 6
  101 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 101 177
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 101 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 101 177 (accept_3_4 4 101 177 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  101 177 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 101 177 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 101 177 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 101 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 101 177 (accept_3_4 1 101 177 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 101 177)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_177_segment_000))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


