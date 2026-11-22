-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch209
-- name    : Polychromatic418967fa_Branch209
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:23:03.440614+00:00
-- url     : https://prove2.me/theorems/2e786265-facd-4c1b-956b-091fdc2d136b
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch209_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_209 : allB 209 209 :=
  allB_succ' 2 208 209 (Eq.refl Bool.true) (allA_of_3_0 2 208 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  207 209 (Eq.refl Bool.true) (allA_succ_of_accept 2 207 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 207 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 207 209 (accept_3_2 1 207 209
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 207 209))) (allB_succ' 4 206 209 (Eq.refl Bool.true)
  (allA_succ_of_accept 3 206 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 206 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 206 209 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 206 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 206 209 (accept_3_2 1 206 209
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 206 209)))) (allB_succ' 5 205 209 (Eq.refl Bool.true) (allA_of_3_0
  5 205 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 6 204 209 (Eq.refl Bool.true) (allA_succ_of_accept 5
  204 209 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 204 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 204 209 (accept_3_2 4 204 209 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 204 209 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 204 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 204 209 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 204 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 204 209 (accept_3_2 1 204 209
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 204 209)))))) (allB_succ' 7 203 209 (Eq.refl Bool.true)
  (allA_succ_of_accept 6 203 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 203 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 203 209 (Polychromatic418967fa.accept_13_5_8_1_1_2161 5 203 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 203 209 (accept_3_2 4 203 209
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 203 209 (Polychromatic418967fa.accept_9_3_5_2_1_28 3
  203 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 203 209
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 203 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 203 209 (accept_3_2 1 203 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 203 209)))))))
  (allB_succ' 8 202 209 (Eq.refl Bool.true) (allA_of_3_0 8 202 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  9 201 209 (Eq.refl Bool.true) (allA_succ_of_accept 8 201 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 201 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 201 209 (accept_3_2 7 201 209
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 201 209 (Polychromatic418967fa.accept_9_6_3_2_1_431 6
  201 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 201 209
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 201 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 201 209 (accept_3_2 4 201 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  201 209 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 201 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 201 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 201 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 201 209 (accept_3_2 1 201 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 201 209))))))))) (allB_succ' 10 200 209 (Eq.refl Bool.true) (allA_succ_of_accept 9 200
  209 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 200 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 200 209 (Polychromatic418967fa.accept_13_8_5_1_1_1381 8 200 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 200 209 (accept_3_2 7 200 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 200 209 (Polychromatic418967fa.accept_13_6_5_1_1_834 6 200 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 200 209 (Polychromatic418967fa.accept_7_5_4_6_1_167 5
  200 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 200 209 (accept_3_2 4 200
  209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 200 209 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 200 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 200 209
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 200 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 200 209 (accept_3_2 1 200 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 200
  209)))))))))) (allB_succ' 11 199 209 (Eq.refl Bool.true) (allA_of_3_0 11 199 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 198 209 (Eq.refl Bool.true) (allA_succ_of_gcd 11 198 209 11 1 18 19 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 198 209 (accept_3_2 10 198 209
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 198 209
  (Polychromatic418967fa.accept_24_9_6_17_1_12324 9 198 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 198 209 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 198 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 198 209 (accept_3_2 7 198 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 198 209 (Polychromatic418967fa.accept_13_6_3_1_1_1413 6 198 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 198 209 (Polychromatic418967fa.accept_13_5_3_1_1_1398
  5 198 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 198 209 (accept_3_2 4
  198 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 198 209
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 198 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 198 209 (Polychromatic418967fa.accept_13_2_3_1_1_3823 2 198 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 198 209 (accept_3_2 1 198 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 198 209)))))))))))) (allB_succ' 13 197 209 (Eq.refl Bool.true) (allA_succ_of_accept 12 197 209
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 197 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 197 209 (Polychromatic418967fa.accept_21_11_8_20_1_4591 11 197 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 197 209 (accept_3_2 10 197 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 197 209 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 197 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 197 209
  (Polychromatic418967fa.accept_10_8_7_9_1_425 8 197 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 197 209 (accept_3_2 7 197 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  197 209 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 197 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 197 209 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 197 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 197 209 (accept_3_2 4 197 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 197 209 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 197 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 197 209
  (Polychromatic418967fa.accept_7_2_1_6_1_173 2 197 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 197 209 (accept_3_2 1 197 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 197
  209))))))))))))) (allB_succ' 14 196 209 (Eq.refl Bool.true) (allA_of_3_0 14 196 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 195 209 (Eq.refl Bool.true) (allA_succ_of_accept 14 195 209
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 195 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 195 209 (accept_3_2 13 195 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 195 209 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 195 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 195 209 (Polychromatic418967fa.accept_10_1_5_9_1_157 11 195 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 195 209 (accept_3_2 10 195 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 195 209 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 195 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 195 209
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 195 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 195 209 (accept_3_2 7 195 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  195 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 195 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 195 209 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 195 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 195 209 (accept_3_2 4 195 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 195 209 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 195 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 195 209
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 195 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 195 209 (accept_3_2 1 195 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 195
  209))))))))))))))) (allB_succ' 16 194 209 (Eq.refl Bool.true) (allA_succ_of_accept 15 194 209
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 194 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 194 209 (Polychromatic418967fa.accept_21_14_5_20_1_12299 14 194 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 194 209 (accept_3_2 13 194 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 194 209 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 194 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 194 209
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 194 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 194 209 (accept_3_2 10 194 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  194 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 194 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 194 209 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 194 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 194 209 (accept_3_2 7 194 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 194 209 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 194 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 194 209
  (Polychromatic418967fa.accept_10_5_4_9_1_420 5 194 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 194 209 (accept_3_2 4 194 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  194 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 194 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 194 209 (Polychromatic418967fa.accept_13_2_12_1_1_343 2 194 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 194 209 (accept_3_2 1 194 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 194 209)))))))))))))))) (allB_succ' 17 193 209 (Eq.refl Bool.true) (allA_of_3_0 17 193
  209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 18 192 209 (Eq.refl Bool.true) (allA_succ_of_accept 17 192
  209 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 192 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 192 209 (accept_3_2 16 192 209 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 192 209 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 192 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 192 209 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 192 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 192 209 (accept_3_2 13 192 209
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 192 209
  (Polychromatic418967fa.accept_21_12_3_20_1_4567 12 192 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 192 209 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 192 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 192 209 (accept_3_2 10 192 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 192 209 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 192 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 192 209
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 192 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 192 209 (accept_3_2 7 192 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  192 209 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 192 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 192 209 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 192 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 192 209 (accept_3_2 4 192 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 192 209 (Polychromatic418967fa.accept_14_3_10_13_1_339 3 192 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 192 209
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 192 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 192 209 (accept_3_2 1 192 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 192
  209)))))))))))))))))) (allB_succ' 19 191 209 (Eq.refl Bool.true) (allA_succ_of_accept 18 191 209
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 191 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 191 209 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 191 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 191 209 (accept_3_2 16 191 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 191 209 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 191 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 191 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 14
  191 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 191 209 (accept_3_2 13
  191 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 191 209
  (Polychromatic418967fa.accept_10_2_1_9_1_1248 12 191 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 191 209 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 191 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 191 209 (accept_3_2 10 191 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 191 209 (Polychromatic418967fa.accept_21_9_2_20_1_857 9 191 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 191 209 (Polychromatic418967fa.accept_7_1_2_6_1_55 8
  191 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 191 209 (accept_3_2 7 191
  209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 191 209 (Polychromatic418967fa.accept_4_2_3_1_1_2
  6 191 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 191 209
  (Polychromatic418967fa.accept_10_5_1_9_1_791 5 191 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 191 209 (accept_3_2 4 191 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  191 209 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 191 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 191 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 191 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 191 209 (accept_3_2 1 191 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 191 209))))))))))))))))))) (allB_succ' 20 190 209 (Eq.refl Bool.true) (allA_of_3_0 20
  190 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 21 189 209 (Eq.refl Bool.true) (allA_succ_of_accept 20
  189 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 189 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 189 209 (accept_3_2 19 189 209 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 189 209 (Polychromatic418967fa.accept_23_18_5_2_1_12323 18 189 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 189 209
  (Polychromatic418967fa.accept_22_17_13_11_1_7413 17 189 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 189 209 (accept_3_2 16 189 209 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 189 209 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 189 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 189 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 189 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 189 209 (accept_3_2 13 189 209
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 189 209 (Polychromatic418967fa.accept_8_4_5_1_1_299
  12 189 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 189 209
  (Polychromatic418967fa.accept_13_11_7_1_1_1386 11 189 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 189 209 (accept_3_2 10 189 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  189 209 (Polychromatic418967fa.accept_16_9_13_1_1_3069 9 189 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 189 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 189 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 189 209 (accept_3_2 7 189 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 189 209 (Polychromatic418967fa.accept_13_6_7_1_1_335 6 189 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 189 209
  (Polychromatic418967fa.accept_15_5_9_14_1_1724 5 189 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 189 209 (accept_3_2 4 189 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  189 209 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 189 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 189 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 189 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 189 209 (accept_3_2 1 189 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 189 209))))))))))))))))))))) (allB_succ' 22 188 209 (Eq.refl Bool.true)
  (allA_succ_of_accept 21 188 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 188 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 188 209 (Polychromatic418967fa.accept_13_7_6_1_1_368 20 188
  209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 188 209 (accept_3_2 19 188
  209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 188 209
  (Polychromatic418967fa.accept_13_5_6_1_1_822 18 188 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 188 209 (Polychromatic418967fa.accept_10_7_8_9_1_785 17 188 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 188 209 (accept_3_2 16 188 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 188 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 188 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 188 209 (Polychromatic418967fa.accept_9_5_8_2_1_409
  14 188 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 188 209 (accept_3_2 13
  188 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 188 209
  (Polychromatic418967fa.accept_9_3_8_2_1_162 12 188 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 188 209 (Polychromatic418967fa.accept_10_1_8_9_1_787 11 188 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 188 209 (accept_3_2 10 188 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 188 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 188 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 188 209 (Polychromatic418967fa.accept_13_8_6_1_1_3808
  8 188 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 188 209 (accept_3_2 7
  188 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 188 209
  (Polychromatic418967fa.accept_9_6_8_2_1_410 6 188 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 188 209 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 188 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 188 209 (accept_3_2 4 188 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 188 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 188 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 188 209 (Polychromatic418967fa.accept_12_2_8_5_1_408 2
  188 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 188 209 (accept_3_2 1 188
  209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 188 209)))))))))))))))))))))) (allB_succ' 23 187 209 (Eq.refl
  Bool.true) (allA_of_3_0 23 187 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 186 209 (Eq.refl Bool.true)
  (allA_succ_of_accept 23 186 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 186 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 186 209 (accept_3_2 22 186 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 186 209 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 186 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 186 209
  (Polychromatic418967fa.accept_15_5_6_14_1_1721 20 186 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 186 209 (accept_3_2 19 186 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 186 209 (Polychromatic418967fa.accept_13_5_4_1_1_364 18 186 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 186 209 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 186 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 186 209 (accept_3_2 16 186 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 186 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 186 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 186 209
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 186 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 186 209 (accept_3_2 13 186 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 186 209 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 186 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 186 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 186 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 186 209 (accept_3_2 10 186 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 186 209 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 186 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 186 209
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 186 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 186 209 (accept_3_2 7 186 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  186 209 (Polychromatic418967fa.accept_21_6_18_20_1_6065 6 186 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 186 209 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 186 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 186 209 (accept_3_2 4 186 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 186 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 186 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 186 209
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 186 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 186 209 (accept_3_2 1 186 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186
  209)))))))))))))))))))))))) (allB_succ' 25 185 209 (Eq.refl Bool.true) (allA_succ_of_accept 24 185 209
  (Polychromatic418967fa.accept_9_6_5_2_1_421 24 185 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 185 209 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 185 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 185 209 (accept_3_2 22 185 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 185 209 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 185 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 185 209 (Polychromatic418967fa.accept_13_7_3_1_1_814
  20 185 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 185 209 (accept_3_2 19
  185 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 185 209
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 185 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 185 209 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 185 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 185 209 (accept_3_2 16 185 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 185 209 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 185 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 185 209 (Polychromatic418967fa.accept_10_4_5_9_1_1231
  14 185 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 185 209 (accept_3_2 13
  185 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 185 209
  (Polychromatic418967fa.accept_9_3_5_2_1_28 12 185 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 185 209 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 185 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 185 209 (accept_3_2 10 185 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 185 209 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 185 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 185 209 (Polychromatic418967fa.accept_9_8_5_2_1_422 8
  185 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 185 209 (accept_3_2 7 185
  209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 185 209
  (Polychromatic418967fa.accept_9_6_5_2_1_421 6 185 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 185 209 (Polychromatic418967fa.accept_13_5_3_1_1_1398 5 185 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 185 209 (accept_3_2 4 185 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 185 209 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 185 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 185 209 (Polychromatic418967fa.accept_7_2_3_6_1_4 2
  185 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 185 209 (accept_3_2 1 185
  209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 185 209))))))))))))))))))))))))) (allB_succ' 26 184 209
  (Eq.refl Bool.true) (allA_of_3_0 26 184 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 27 183 209 (Eq.refl
  Bool.true) (allA_succ_of_accept 26 183 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 183 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 183 209 (accept_3_2 25 183 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 183 209 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 183 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 183 209
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 183 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 183 209 (accept_3_2 22 183 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 183 209 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 183 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 183 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 183 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 183 209 (accept_3_2 19 183 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 183 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 183 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 183 209
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 183 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 183 209 (accept_3_2 16 183 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 183 209 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 183 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 183 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 183 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 183 209 (accept_3_2 13 183 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 183 209 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 183 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 183 209
  (Polychromatic418967fa.accept_15_11_3_14_1_971 11 183 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 183 209 (accept_3_2 10 183 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  183 209 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 183 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 183 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 183 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 183 209 (accept_3_2 7 183 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 183 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 183 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 183 209
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 183 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 183 209 (accept_3_2 4 183 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  183 209 (Polychromatic418967fa.accept_23_3_22_2_1_12322 3 183 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 183 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 183 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 183 209 (accept_3_2 1 183 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 183 209))))))))))))))))))))))))))) (allB_succ' 28 182 209 (Eq.refl Bool.true)
  (allA_succ_of_accept 27 182 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 182 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 182 209 (Polychromatic418967fa.accept_17_9_12_5_1_219 26 182
  209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 182 209 (accept_3_2 25 182
  209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 182 209
  (Polychromatic418967fa.accept_17_7_12_5_1_1580 24 182 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 182 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 182 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 182 209 (accept_3_2 22 182 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 182 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 182 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 182 209 (Polychromatic418967fa.accept_12_8_2_5_1_844
  20 182 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 182 209 (accept_3_2 19
  182 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 182 209
  (Polychromatic418967fa.accept_15_3_2_14_1_1713 18 182 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 182 209 (Polychromatic418967fa.accept_10_7_2_9_1_775 17 182 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 182 209 (accept_3_2 16 182 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 182 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 182 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 182 209
  (Polychromatic418967fa.accept_18_14_2_11_1_4384 14 182 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 182 209 (accept_3_2 13 182 209 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 182 209 (Polychromatic418967fa.accept_15_12_2_14_1_5659 12 182 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 182 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 11
  182 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 182 209 (accept_3_2 10
  182 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 182 209
  (Polychromatic418967fa.accept_6_3_2_5_1_32 9 182 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 182 209 (Polychromatic418967fa.accept_12_8_2_5_1_844 8 182 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 182 209 (accept_3_2 7 182 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 182 209 (Polychromatic418967fa.accept_21_6_14_20_1_4594 6 182 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 182 209
  (Polychromatic418967fa.accept_15_5_2_14_1_1693 5 182 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 182 209 (accept_3_2 4 182 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  182 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 182 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 182 209 (Polychromatic418967fa.accept_16_2_6_1_1_2069 2 182 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 182 209 (accept_3_2 1 182 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 182 209)))))))))))))))))))))))))))) (allB_succ' 29 181 209 (Eq.refl Bool.true)
  (allA_of_3_0 29 181 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 30 180 209 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 180 209 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 180 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 180 209 (accept_3_2 28 180 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 180 209 (Polychromatic418967fa.accept_22_5_4_11_1_12321 27 180 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 180 209
  (Polychromatic418967fa.accept_25_1_5_9_1_12320 26 180 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 180 209 (accept_3_2 25 180 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 180 209 (Polychromatic418967fa.accept_16_8_4_1_1_2102 24 180 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 180 209 (Polychromatic418967fa.accept_13_10_11_1_1_2152 23 180 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 180 209 (accept_3_2 22 180 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 180 209 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 180 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 180 209
  (Polychromatic418967fa.accept_13_7_11_1_1_2903 20 180 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 180 209 (accept_3_2 19 180 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 180 209 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 180 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 180 209 (Polychromatic418967fa.accept_22_17_4_11_1_7403 17 180 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 180 209 (accept_3_2 16 180 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 180 209 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 180 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 180 209
  (Polychromatic418967fa.accept_16_14_4_1_1_3049 14 180 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 180 209 (accept_3_2 13 180 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 180 209 (Polychromatic418967fa.accept_13_12_11_1_1_2920 12 180 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 180 209 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 180 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 180 209 (accept_3_2 10 180 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 180 209 (Polychromatic418967fa.accept_13_9_11_1_1_1375 9 180 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 180 209
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 180 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 180 209 (accept_3_2 7 180 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  180 209 (Polychromatic418967fa.accept_14_6_12_13_1_3180 6 180 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 180 209 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 180 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 180 209 (accept_3_2 4 180 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 180 209 (Polychromatic418967fa.accept_13_3_11_1_1_2122 3 180 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 180 209
  (Polychromatic418967fa.accept_25_2_5_9_1_6819 2 180 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 180 209 (accept_3_2 1 180 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 180
  209)))))))))))))))))))))))))))))) (allB_succ' 31 179 209 (Eq.refl Bool.true) (allA_succ_of_accept 30 179 209
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 179 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 179 209 (Polychromatic418967fa.accept_16_13_3_1_1_2100 29 179 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 179 209 (accept_3_2 28 179 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 179 209 (Polychromatic418967fa.accept_21_6_11_20_1_10794 27 179 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 179 209
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 179 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 179 209 (accept_3_2 25 179 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 179 209 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 179 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 179 209 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 179 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 179 209 (accept_3_2 22 179 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 179 209 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 179 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 179 209
  (Polychromatic418967fa.accept_16_4_3_1_1_8843 20 179 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 179 209 (accept_3_2 19 179 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 179 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 179 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 179 209 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 179 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 179 209 (accept_3_2 16 179 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 179 209 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 179 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 179 209
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 179 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 179 209 (accept_3_2 13 179 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 179 209 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 179 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 179 209 (Polychromatic418967fa.accept_13_11_10_1_1_1409 11 179 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 179 209 (accept_3_2 10 179 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 179 209 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 179 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 179 209
  (Polychromatic418967fa.accept_20_8_19_9_1_6417 8 179 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 179 209 (accept_3_2 7 179 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  179 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 179 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 179 209 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 179 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 179 209 (accept_3_2 4 179 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 179 209 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 179 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 179 209
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 179 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 179 209 (accept_3_2 1 179 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 179
  209))))))))))))))))))))))))))))))) (allB_succ' 32 178 209 (Eq.refl Bool.true) (allA_of_3_0 32 178 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 177 209 (Eq.refl Bool.true) (allA_succ_of_accept 32 177 209
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 177 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 177 209 (accept_3_2 31 177 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 177 209 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 177 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 177 209 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 177 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 177 209 (accept_3_2 28 177 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 177 209 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 177 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 177 209
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 177 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 177 209 (accept_3_2 25 177 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 177 209 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 177 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 177 209 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 177 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 177 209 (accept_3_2 22 177 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 177 209 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 177 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 177 209
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 177 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 177 209 (accept_3_2 19 177 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 177 209 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 177 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 177 209 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 177 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 177 209 (accept_3_2 16 177 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 177 209 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 177 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 177 209
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 177 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 177 209 (accept_3_2 13 177 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 177 209 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 177 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 177 209 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 177 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 177 209 (accept_3_2 10 177 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 177 209 (Polychromatic418967fa.accept_13_9_8_1_1_824 9 177 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 177 209
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 177 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 177 209 (accept_3_2 7 177 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  177 209 (Polychromatic418967fa.accept_13_6_8_1_1_2913 6 177 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 177 209 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 177 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 177 209 (accept_3_2 4 177 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 177 209 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 177 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 177 209
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 177 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 177 209 (accept_3_2 1 177 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 177
  209))))))))))))))))))))))))))))))))) (allB_succ' 34 176 209 (Eq.refl Bool.true) (allA_succ_of_gcd 33 176 209 11 3 16
  19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 176 209
  (Polychromatic418967fa.accept_13_6_7_1_1_335 32 176 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 176 209 (accept_3_2 31 176 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 176 209 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 176 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 176 209 (Polychromatic418967fa.accept_13_3_7_1_1_334 29 176 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 176 209 (accept_3_2 28 176 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 176 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 176 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 176 209
  (Polychromatic418967fa.accept_7_5_1_6_1_163 26 176 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 176 209 (accept_3_2 25 176 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 176 209 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 176 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 176 209 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 176 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 176 209 11 2 16 19 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 176 209
  (Polychromatic418967fa.accept_6_3_2_5_1_32 21 176 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 176 209 (Polychromatic418967fa.accept_17_3_6_5_1_8669 20 176 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 176 209 (accept_3_2 19 176 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 176 209 (Polychromatic418967fa.accept_15_3_11_14_1_1705 18 176 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 176 209
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 176 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 176 209 (accept_3_2 16 176 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 176 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 176 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 176 209 (Polychromatic418967fa.accept_12_2_8_5_1_408 14 176 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 176 209 (accept_3_2 13 176 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 176 209 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 176 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 11 176 209 11 1 16 19 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 176 209 (accept_3_2 10
  176 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 176 209
  (Polychromatic418967fa.accept_6_3_2_5_1_32 9 176 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 176 209 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 176 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 176 209 (accept_3_2 7 176 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 176 209 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 176 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 176 209 (Polychromatic418967fa.accept_7_5_1_6_1_163 5
  176 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 176 209 (accept_3_2 4 176
  209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 176 209 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 176 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 176 209
  (Polychromatic418967fa.accept_7_2_1_6_1_173 2 176 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 176 209 (accept_3_2 1 176 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 176
  209)))))))))))))))))))))))))))))))))) (allB_succ' 35 175 209 (Eq.refl Bool.true) (allA_of_3_0 35 175 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 174 209 (Eq.refl Bool.true) (allA_succ_of_accept 35 174 209
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 174 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 174 209 (accept_3_2 34 174 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 174 209 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 174 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 174 209 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 174 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 174 209 (accept_3_2 31 174 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 174 209 (Polychromatic418967fa.accept_13_4_5_1_1_833 30 174 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 174 209
  (Polychromatic418967fa.accept_13_3_5_1_1_2144 29 174 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 174 209 (accept_3_2 28 174 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 174 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 174 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 174 209 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 174 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 174 209 (accept_3_2 25 174 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 174 209 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 174 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 174 209
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 174 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 174 209 (accept_3_2 22 174 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 174 209 (Polychromatic418967fa.accept_13_8_5_1_1_1381 21 174 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 174 209 (Polychromatic418967fa.accept_15_5_9_14_1_1724 20 174 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 174 209 (accept_3_2 19 174 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 174 209 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 174
  209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 174 209
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 174 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 174 209 (accept_3_2 16 174 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 174 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 174 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 174 209 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 174 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 174 209 (accept_3_2 13 174 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 174 209 (Polychromatic418967fa.accept_13_12_5_1_1_1383 12 174 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 174 209
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 174 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 174 209 (accept_3_2 10 174 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  174 209 (Polychromatic418967fa.accept_13_9_5_1_1_1382 9 174 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 174 209 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 174 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 174 209 (accept_3_2 7 174 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 174 209 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 174 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 174 209
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 174 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 174 209 (accept_3_2 4 174 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  174 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 174 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 174 209 (Polychromatic418967fa.accept_21_2_6_20_1_6059 2 174 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 174 209 (accept_3_2 1 174 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 174 209)))))))))))))))))))))))))))))))))))) (allB_succ' 37 173 209 (Eq.refl
  Bool.true) (allA_succ_of_accept 36 173 209 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 173 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 173 209 (Polychromatic418967fa.accept_15_5_8_14_1_432
  35 173 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 173 209 (accept_3_2 34
  173 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 173 209
  (Polychromatic418967fa.accept_23_10_12_2_1_12319 33 173 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 173 209 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 173 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 173 209 (accept_3_2 31 173 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 173 209 (Polychromatic418967fa.accept_16_14_13_1_1_5278 30 173 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 173 209
  (Polychromatic418967fa.accept_7_1_5_6_1_59 29 173 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 173 209 (accept_3_2 28 173 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 173 209 (Polychromatic418967fa.accept_21_6_5_20_1_12265 27 173 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 173 209 (Polychromatic418967fa.accept_10_6_3_9_1_1207 26 173 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 173 209 (accept_3_2 25 173 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 173 209 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 173
  209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 173 209
  (Polychromatic418967fa.accept_13_10_4_1_1_2142 23 173 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 173 209 (accept_3_2 22 173 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 173 209 (Polychromatic418967fa.accept_15_6_8_14_1_4575 21 173 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 173 209 (Polychromatic418967fa.accept_8_4_5_1_1_299 20 173 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 173 209 (accept_3_2 19 173 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 173 209 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 173 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 173 209
  (Polychromatic418967fa.accept_27_17_11_20_1_12318 17 173 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 173 209 (accept_3_2 16 173 209 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 173 209 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 173 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 173 209 (Polychromatic418967fa.accept_10_4_3_9_1_1262 14 173
  209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 173 209 (accept_3_2 13 173
  209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 173 209
  (Polychromatic418967fa.accept_8_4_5_1_1_299 12 173 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 173 209 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 173 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 173 209 (accept_3_2 10 173 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 173 209 (Polychromatic418967fa.accept_15_9_8_14_1_1699 9 173 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 173 209
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 173 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 173 209 (accept_3_2 7 173 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  173 209 (Polychromatic418967fa.accept_10_6_3_9_1_1207 6 173 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 173 209 (Polychromatic418967fa.accept_13_5_4_1_1_364 5 173 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 173 209 (accept_3_2 4 173 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 173 209 (Polychromatic418967fa.accept_13_3_4_1_1_363 3 173 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 173 209
  (Polychromatic418967fa.accept_17_2_3_5_1_763 2 173 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 173 209 (accept_3_2 1 173 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 173
  209))))))))))))))))))))))))))))))))))))) (allB_succ' 38 172 209 (Eq.refl Bool.true) (allA_of_3_0 38 172 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 171 209 (Eq.refl Bool.true) (allA_succ_of_gcd 38 171 209 19 2 9 11
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 171 209
  (accept_3_2 37 171 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 171 209
  (Polychromatic418967fa.accept_24_12_3_17_1_12317 36 171 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 171 209 (Polychromatic418967fa.accept_10_5_1_9_1_791 35 171 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 171 209 (accept_3_2 34 171 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 171 209 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 171
  209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 171 209
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 171 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 171 209 (accept_3_2 31 171 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 171 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 171 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 171 209 (Polychromatic418967fa.accept_13_3_2_1_1_2907 29 171 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 171 209 (accept_3_2 28 171 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 171 209 (Polychromatic418967fa.accept_21_6_3_20_1_6053 27 171
  209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 171 209
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 171 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 171 209 (accept_3_2 25 171 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 171 209 (Polychromatic418967fa.accept_14_10_3_13_1_1530 24 171 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 171 209 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 171 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 171 209 (accept_3_2 22 171 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 171 209 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 171 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 171 209
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 171 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 19 171 209 19 1 9 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 18 171 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 171 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 171 209 (Polychromatic418967fa.accept_21_17_3_20_1_6054 17 171
  209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 171 209 (accept_3_2 16 171
  209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 171 209
  (Polychromatic418967fa.accept_10_5_1_9_1_791 15 171 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 171 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 171 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 171 209 (accept_3_2 13 171 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 171 209 (Polychromatic418967fa.accept_10_2_1_9_1_1248 12 171 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 171 209
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 171 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 171 209 (accept_3_2 10 171 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  171 209 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 171 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 171 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 171 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 209 (accept_3_2 7 171 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 171 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 171 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 171 209
  (Polychromatic418967fa.accept_10_5_1_9_1_791 5 171 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 171 209 (accept_3_2 4 171 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  171 209 (Polychromatic418967fa.accept_13_3_2_1_1_2907 3 171 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 171 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 171 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 209 (accept_3_2 1 171 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 171 209))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 170 209 (Eq.refl
  Bool.true) (allA_succ_of_accept 39 170 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 170 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 170 209 (Polychromatic418967fa.accept_7_3_2_6_1_56 38
  170 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 170 209 (accept_3_2 37
  170 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 170 209
  (Polychromatic418967fa.accept_7_1_2_6_1_55 36 170 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 170 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 170 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 170 209 (accept_3_2 34 170 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 170 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 170 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 170 209 (Polychromatic418967fa.accept_7_4_2_6_1_337
  32 170 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 170 209 (accept_3_2 31
  170 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 170 209
  (Polychromatic418967fa.accept_9_3_8_2_1_162 30 170 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 170 209 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 170 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 170 209 (accept_3_2 28 170 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 170 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 170 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 170 209
  (Polychromatic418967fa.accept_20_6_10_9_1_3486 26 170 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 170 209 (accept_3_2 25 170 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 170 209 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 170 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 170 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 170 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 170 209 (accept_3_2 22 170 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 170 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 170 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 170 209
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 170 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 170 209 (accept_3_2 19 170 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 170 209 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 170 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 170 209 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 170 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 170 209 (accept_3_2 16 170 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 170 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 170 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 170 209
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 170 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 170 209 (accept_3_2 13 170 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 170 209 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 170 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 170 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 170 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 170 209 (accept_3_2 10 170 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 170 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 170 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 170 209
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 170 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 170 209 (accept_3_2 7 170 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  170 209 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 170 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 170 209 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 170 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 170 209 (accept_3_2 4 170 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 170 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 170 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 170 209
  (Polychromatic418967fa.accept_15_2_5_14_1_61 2 170 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 170 209 (accept_3_2 1 170 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 170
  209)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 169 209 (Eq.refl Bool.true) (allA_of_3_0 41 169 209
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 168 209 (Eq.refl Bool.true) (allA_succ_of_accept 41 168 209
  (Polychromatic418967fa.accept_9_5_6_2_1_161 41 168 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 168 209 (accept_3_2 40 168 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 168 209 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 168 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 168 209 (Polychromatic418967fa.accept_23_15_7_2_1_12316 38 168 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 168 209 (accept_3_2 37 168 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 168 209 (Polychromatic418967fa.accept_16_4_8_1_1_5257 36 168
  209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 168 209
  (Polychromatic418967fa.accept_9_8_6_2_1_744 35 168 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 168 209 (accept_3_2 34 168 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 168 209 (Polychromatic418967fa.accept_18_15_6_11_1_5651 33 168 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 168 209 (Polychromatic418967fa.accept_9_5_6_2_1_161 32 168 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 168 209 (accept_3_2 31 168 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 168 209 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 168 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 168 209
  (Polychromatic418967fa.accept_25_4_18_9_1_12315 29 168 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 168 209 (accept_3_2 28 168 209 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 168 209 (Polychromatic418967fa.accept_10_7_8_9_1_785 27 168 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 168 209 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 168 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 168 209 (accept_3_2 25 168 209
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 168 209 (Polychromatic418967fa.accept_10_4_8_9_1_784
  24 168 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 168 209
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 168 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 168 209 (accept_3_2 22 168 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 168 209 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 168 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 168 209 (Polychromatic418967fa.accept_16_4_8_1_1_5257 20 168 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 168 209 (accept_3_2 19 168 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 168 209 (Polychromatic418967fa.accept_13_5_12_1_1_2123 18 168
  209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 168 209
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 168 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 168 209 (accept_3_2 16 168 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 168 209 (Polychromatic418967fa.accept_13_2_12_1_1_343 15 168 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 168 209 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 168 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 168 209 (accept_3_2 13 168 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 168 209 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 168 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 168 209
  (Polychromatic418967fa.accept_10_1_8_9_1_787 11 168 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 168 209 (accept_3_2 10 168 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  168 209 (Polychromatic418967fa.accept_16_9_8_1_1_1228 9 168 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 168 209 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 168 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 168 209 (accept_3_2 7 168 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 168 209 (Polychromatic418967fa.accept_25_6_18_9_1_12314 6 168 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 168 209
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 168 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 168 209 (accept_3_2 4 168 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  168 209 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 168 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 168 209 (Polychromatic418967fa.accept_13_2_12_1_1_343 2 168 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 168 209 (accept_3_2 1 168 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 168 209)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 167 209 (Eq.refl
  Bool.true) (allA_succ_of_accept 42 167 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 167 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 167 209
  (Polychromatic418967fa.accept_22_19_13_11_1_12313 41 167 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 167 209 (accept_3_2 40 167 209 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 167 209 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 167 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 167 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 167 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 167 209 (accept_3_2 37 167 209
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 167 209
  (Polychromatic418967fa.accept_13_10_11_1_1_2152 36 167 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 167 209 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 167 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 167 209 (accept_3_2 34 167 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 167 209 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 167 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 167 209
  (Polychromatic418967fa.accept_10_2_7_9_1_783 32 167 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 167 209 (accept_3_2 31 167 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 167 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 167 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 167 209 (Polychromatic418967fa.accept_13_3_11_1_1_2122 29 167 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 167 209 (accept_3_2 28 167 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 167 209 (Polychromatic418967fa.accept_15_12_2_14_1_5659 27 167
  209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 167 209
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 167 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 167 209 (accept_3_2 25 167 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 167 209 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 167 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 167 209 (Polychromatic418967fa.accept_13_10_11_1_1_2152 23 167 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 167 209 (accept_3_2 22 167 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 167 209 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 167 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 167 209
  (Polychromatic418967fa.accept_13_7_11_1_1_2903 20 167 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 167 209 (accept_3_2 19 167 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 167 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 167 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 167 209 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 167 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 167 209 (accept_3_2 16 167 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 167 209 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 167 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 167 209
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 167 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 167 209 (accept_3_2 13 167 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 167 209 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 167 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 167 209 (Polychromatic418967fa.accept_24_11_23_17_1_7012 11 167 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 167 209 (accept_3_2 10 167 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 167 209 (Polychromatic418967fa.accept_13_9_11_1_1_1375 9 167
  209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 167 209
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 167 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 167 209 (accept_3_2 7 167 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  167 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 167 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 167 209 (Polychromatic418967fa.accept_15_5_2_14_1_1693 5 167 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 167 209 (accept_3_2 4 167 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 167 209 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 167 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 167 209
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 167 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 167 209 (accept_3_2 1 167 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 167
  209))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 166 209 (Eq.refl Bool.true) (allA_of_3_0 44 166 209
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 165 209 (Eq.refl Bool.true) (allA_succ_of_gcd 44 165 209 11 4
  15 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 165 209
  (accept_3_2 43 165 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 165 209
  (Polychromatic418967fa.accept_9_6_3_2_1_431 42 165 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 165 209 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 165 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 165 209 (accept_3_2 40 165 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 165 209 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 165 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 165 209
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 165 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 165 209 (accept_3_2 37 165 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 165 209 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 165 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 165 209 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 165 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 165 209 (accept_3_2 34 165 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 33 165 209 11 3 15 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 165 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 165 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 165 209 (accept_3_2 31 165 209
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 165 209 (Polychromatic418967fa.accept_7_2_4_6_1_166
  30 165 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 165 209
  (Polychromatic418967fa.accept_16_13_5_1_1_3017 29 165 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 165 209 (accept_3_2 28 165 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 165 209 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 165 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 165 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 165 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 165 209 (accept_3_2 25 165 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 165 209 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 165 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 165 209
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 165 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 165 209 11 2 15 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 165 209 (Polychromatic418967fa.accept_10_1_5_9_1_157 21 165 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 165 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 20
  165 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 165 209 (accept_3_2 19
  165 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 165 209
  (Polychromatic418967fa.accept_13_5_9_1_1_1405 18 165 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 165 209 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 165 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 165 209 (accept_3_2 16 165 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 165 209 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 165 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 165 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 14
  165 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 165 209 (accept_3_2 13
  165 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 165 209
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 165 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 11 165 209 11 1 15 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 10 165 209 (accept_3_2 10 165 209 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 165 209 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 165 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 165 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 165 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 209 (accept_3_2 7 165 209
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 165 209 (Polychromatic418967fa.accept_9_6_3_2_1_431 6
  165 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 165 209
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 165 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 165 209 (accept_3_2 4 165 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  165 209 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 165 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 165 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 165 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 209 (accept_3_2 1 165 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 165 209))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 164 209 (Eq.refl
  Bool.true) (allA_succ_of_accept 45 164 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 164 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 164 209 (Polychromatic418967fa.accept_7_2_3_6_1_4 44
  164 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 164 209 (accept_3_2 43
  164 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 164 209
  (Polychromatic418967fa.accept_20_2_4_9_1_9524 42 164 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 164 209 (Polychromatic418967fa.accept_17_7_11_5_1_3539 41 164 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 164 209 (accept_3_2 40 164 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 164 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 164 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 164 209 (Polychromatic418967fa.accept_10_8_4_9_1_1229
  38 164 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 164 209 (accept_3_2 37
  164 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 164 209
  (Polychromatic418967fa.accept_22_14_10_11_1_7472 36 164 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 164 209 (Polychromatic418967fa.accept_10_5_4_9_1_420 35 164 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 164 209 (accept_3_2 34 164 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 164 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 164 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 164 209
  (Polychromatic418967fa.accept_7_4_3_6_1_340 32 164 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 164 209 (accept_3_2 31 164 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 164 209 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 164 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 164 209 (Polychromatic418967fa.accept_8_5_4_1_1_111 29 164 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 164 209 (accept_3_2 28 164 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 164 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 164 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 164 209
  (Polychromatic418967fa.accept_12_2_8_5_1_408 26 164 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 164 209 (accept_3_2 25 164 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 164 209 (Polychromatic418967fa.accept_13_11_8_1_1_3815 24 164 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 164 209 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 164 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 164 209 (accept_3_2 22 164 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 164 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 164 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 164 209
  (Polychromatic418967fa.accept_13_7_8_1_1_2145 20 164 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 164 209 (accept_3_2 19 164 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 164 209 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 164 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 164 209 (Polychromatic418967fa.accept_14_3_10_13_1_339 17 164 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 164 209 (accept_3_2 16 164 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 164 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 164 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 164 209
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 164 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 164 209 (accept_3_2 13 164 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 164 209 (Polychromatic418967fa.accept_13_12_8_1_1_825 12 164 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 164 209 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 164 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 164 209 (accept_3_2 10 164 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 164 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 164 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 164 209
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 164 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 164 209 (accept_3_2 7 164 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  164 209 (Polychromatic418967fa.accept_13_6_8_1_1_2913 6 164 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 164 209 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 164 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 164 209 (accept_3_2 4 164 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 164 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 164 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 164 209
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 164 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 164 209 (accept_3_2 1 164 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 164
  209)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 163 209 (Eq.refl Bool.true) (allA_of_3_0 47 163 209
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 162 209 (Eq.refl Bool.true) (allA_succ_of_accept 47 162 209
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 162 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 162 209 (accept_3_2 46 162 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 162 209 (Polychromatic418967fa.accept_22_1_8_11_1_12312 45 162 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 162 209 (Polychromatic418967fa.accept_7_2_1_6_1_173 44 162 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 162 209 (accept_3_2 43 162 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 162 209 (Polychromatic418967fa.accept_13_3_6_1_1_3797 42 162 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 162 209
  (Polychromatic418967fa.accept_10_1_2_9_1_152 41 162 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 162 209 (accept_3_2 40 162 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 162 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 162 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 162 209 (Polychromatic418967fa.accept_16_6_2_1_1_4081 38 162 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 162 209 (accept_3_2 37 162 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 162 209 (Polychromatic418967fa.accept_22_14_8_11_1_2777 36 162
  209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 162 209
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 162 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 162 209 (accept_3_2 34 162 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 162 209 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 162 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 162 209 (Polychromatic418967fa.accept_15_2_12_14_1_1709 32 162 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 162 209 (accept_3_2 31 162 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 162 209 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 162 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 162 209
  (Polychromatic418967fa.accept_13_3_6_1_1_3797 29 162 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 162 209 (accept_3_2 28 162 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 162 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 162 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 162 209 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 162 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 162 209 (accept_3_2 25 162 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 162 209 (Polychromatic418967fa.accept_15_9_12_14_1_963 24 162 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 162 209
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 162 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 162 209 (accept_3_2 22 162 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 162 209 (Polychromatic418967fa.accept_10_1_2_9_1_152 21 162 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 162 209 (Polychromatic418967fa.accept_13_7_6_1_1_368 20 162 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 162 209 (accept_3_2 19 162 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 162 209 (Polychromatic418967fa.accept_13_5_6_1_1_822 18 162
  209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 162 209
  (Polychromatic418967fa.accept_10_7_2_9_1_775 17 162 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 162 209 (accept_3_2 16 162 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 162 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 162 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 162 209 (Polychromatic418967fa.accept_17_14_9_5_1_4755 14 162 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 162 209 (accept_3_2 13 162 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 162 209 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 162 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 162 209
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 162 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 162 209 (accept_3_2 10 162 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  162 209 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 162 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 162 209 (Polychromatic418967fa.accept_13_8_6_1_1_3808 8 162 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 162 209 (accept_3_2 7 162 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 162 209 (Polychromatic418967fa.accept_16_6_2_1_1_4081 6 162 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 162 209
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 162 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 162 209 (accept_3_2 4 162 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  162 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 162 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 162 209 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 162 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 162 209 (accept_3_2 1 162 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 162 209)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 161 209 (Eq.refl
  Bool.true) (allA_succ_of_accept 48 161 209 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 161 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 161 209 (Polychromatic418967fa.accept_13_8_5_1_1_1381
  47 161 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 161 209 (accept_3_2 46
  161 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 161 209
  (Polychromatic418967fa.accept_10_5_1_9_1_791 45 161 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 161 209 (Polychromatic418967fa.accept_21_2_14_20_1_841 44 161 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 161 209 (accept_3_2 43 161 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 161 209 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 161 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 161 209 (Polychromatic418967fa.accept_9_5_8_2_1_409
  41 161 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 161 209 (accept_3_2 40
  161 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 161 209
  (Polychromatic418967fa.accept_9_3_8_2_1_162 39 161 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 161 209 (Polychromatic418967fa.accept_10_8_1_9_1_413 38 161 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 161 209 (accept_3_2 37 161 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 161 209 (Polychromatic418967fa.accept_14_8_7_13_1_4113 36 161 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 161 209
  (Polychromatic418967fa.accept_10_5_1_9_1_791 35 161 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 161 209 (accept_3_2 34 161 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 161 209 (Polychromatic418967fa.accept_9_6_8_2_1_410 33 161 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 161 209 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 161 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 161 209 (accept_3_2 31 161 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 161 209 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 161 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 161 209
  (Polychromatic418967fa.accept_13_3_5_1_1_2144 29 161 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 161 209 (accept_3_2 28 161 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 161 209 (Polychromatic418967fa.accept_15_12_11_14_1_3464 27 161 209 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 26 161 209 (Polychromatic418967fa.accept_21_5_14_20_1_9265 26 161 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 161 209 (accept_3_2 25 161 209
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 161 209 (Polychromatic418967fa.accept_9_6_8_2_1_410
  24 161 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 161 209
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 161 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 161 209 (accept_3_2 22 161 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 161 209 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 161 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 161 209 (Polychromatic418967fa.accept_14_6_7_13_1_3158 20 161 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 161 209 (accept_3_2 19 161 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 161 209 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 161
  209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 161 209
  (Polychromatic418967fa.accept_13_4_5_1_1_833 17 161 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 161 209 (accept_3_2 16 161 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 161 209 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 161 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 161 209 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 161 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 161 209 (accept_3_2 13 161 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 161 209 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 161 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 161 209
  (Polychromatic418967fa.accept_21_11_14_20_1_12235 11 161 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 161 209 (accept_3_2 10 161 209 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 161 209 (Polychromatic418967fa.accept_13_9_5_1_1_1382 9 161 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 161 209 (Polychromatic418967fa.accept_10_8_1_9_1_413 8 161 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 161 209 (accept_3_2 7 161 209
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 161 209 (Polychromatic418967fa.accept_9_6_8_2_1_410 6
  161 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 161 209
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 161 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 161 209 (accept_3_2 4 161 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  161 209 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 161 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 161 209 (Polychromatic418967fa.accept_10_2_1_9_1_1248 2 161 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 161 209 (accept_3_2 1 161 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 161 209))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 160 209
  (Eq.refl Bool.true) (allA_of_3_0 50 160 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 159 209 (Eq.refl
  Bool.true) (allA_succ_of_accept 50 159 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 159 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 159 209 (accept_3_2 49 159 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 159 209 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 159 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 159 209
  (Polychromatic418967fa.accept_31_16_4_23_1_12311 47 159 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 159 209 (accept_3_2 46 159 209 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 159 209 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 159 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 159 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 159 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 159 209 (accept_3_2 43 159 209
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 159 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 42
  159 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 159 209
  (Polychromatic418967fa.accept_9_5_6_2_1_161 41 159 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 159 209 (accept_3_2 40 159 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 159 209 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 159 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 159 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 159 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 159 209 (accept_3_2 37 159 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 159 209 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 159 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 159 209
  (Polychromatic418967fa.accept_9_8_6_2_1_744 35 159 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 159 209 (accept_3_2 34 159 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 159 209 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 159 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 159 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 159 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 159 209 (accept_3_2 31 159 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 159 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 159 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 159 209
  (Polychromatic418967fa.accept_7_1_5_6_1_59 29 159 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 159 209 (accept_3_2 28 159 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 159 209 (Polychromatic418967fa.accept_15_12_9_14_1_2635 27 159 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 159 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 159 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 159 209 (accept_3_2 25 159 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 159 209 (Polychromatic418967fa.accept_13_11_3_1_1_1397 24 159 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 159 209
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 159 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 159 209 (accept_3_2 22 159 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 159 209 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 159 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 159 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 159 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 159 209 (accept_3_2 19 159 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 159 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 159 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 159 209
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 159 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 159 209 (accept_3_2 16 159 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 159 209 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 159 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 159 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 159 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 209 (accept_3_2 13 159 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 159 209 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 159 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 159 209
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 159 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 159 209 (accept_3_2 10 159 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  159 209 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 159 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 159 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 159 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 209 (accept_3_2 7 159 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 159 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 159 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 159 209
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 159 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 159 209 (accept_3_2 4 159 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  159 209 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 159 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 159 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 159 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 209 (accept_3_2 1 159 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 159 209))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 158 209
  (Eq.refl Bool.true) (allA_succ_of_accept 51 158 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 158 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 158 209
  (Polychromatic418967fa.accept_15_5_8_14_1_432 50 158 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 158 209 (accept_3_2 49 158 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 158 209 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 158 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 158 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 158 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 158 209 (accept_3_2 46 158 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 158 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 158 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 158 209
  (Polychromatic418967fa.accept_7_2_4_6_1_166 44 158 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 158 209 (accept_3_2 43 158 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 158 209 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 158 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 158 209 (Polychromatic418967fa.accept_10_1_8_9_1_787 41 158 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 158 209 (accept_3_2 40 158 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 158 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 158 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 158 209
  (Polychromatic418967fa.accept_7_3_4_6_1_329 38 158 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 158 209 (accept_3_2 37 158 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 158 209 (Polychromatic418967fa.accept_15_6_8_14_1_4575 36 158 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 158 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 158 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 158 209 (accept_3_2 34 158 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 158 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 158 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 158 209
  (Polychromatic418967fa.accept_12_8_2_5_1_844 32 158 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 158 209 (accept_3_2 31 158 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 158 209 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 158 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 158 209 (Polychromatic418967fa.accept_13_3_2_1_1_2907 29 158 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 158 209 (accept_3_2 28 158 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 158 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 158 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 158 209
  (Polychromatic418967fa.accept_7_5_4_6_1_167 26 158 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 158 209 (accept_3_2 25 158 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 158 209 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 158 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 158 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 158 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 158 209 (accept_3_2 22 158 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 158 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 158 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 158 209
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 158 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 158 209 (accept_3_2 19 158 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 158 209 (Polychromatic418967fa.accept_21_18_11_20_1_3154 18 158 209 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 17 158 209 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 158 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 158 209 (accept_3_2 16 158 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 158 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 158 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 158 209
  (Polychromatic418967fa.accept_10_4_8_9_1_784 14 158 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 158 209 (accept_3_2 13 158 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 158 209 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 158 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 158 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 158 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 158 209 (accept_3_2 10 158 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 158 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 158 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 158 209
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 158 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 158 209 (accept_3_2 7 158 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  158 209 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 158 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 158 209 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 158 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 158 209 (accept_3_2 4 158 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 158 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 158 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 158 209
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 158 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 158 209 (accept_3_2 1 158 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158
  209)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 157 209 (Eq.refl Bool.true) (allA_of_3_0 53 157
  209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 54 156 209 (Eq.refl Bool.true) (allA_succ_of_accept 53 156
  209 (Polychromatic418967fa.accept_7_4_2_6_1_337 53 156 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 156 209 (accept_3_2 52 156 209 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 156 209 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 156 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 156 209 (Polychromatic418967fa.accept_7_1_2_6_1_55 50 156 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 156 209 (accept_3_2 49 156 209
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 156 209
  (Polychromatic418967fa.accept_21_6_9_20_1_3190 48 156 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 156 209 (Polychromatic418967fa.accept_20_7_16_9_1_4970 47 156 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 156 209 (accept_3_2 46 156 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 156 209 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 156 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 156 209 (Polychromatic418967fa.accept_9_8_3_2_1_417
  44 156 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 156 209 (accept_3_2 43
  156 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 156 209
  (Polychromatic418967fa.accept_9_6_3_2_1_431 42 156 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 156 209 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 156 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 156 209 (accept_3_2 40 156 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 156 209 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 156 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 156 209 (Polychromatic418967fa.accept_7_3_2_6_1_56 38
  156 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 156 209 (accept_3_2 37
  156 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 156 209
  (Polychromatic418967fa.accept_7_1_2_6_1_55 36 156 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 156 209 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 156 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 156 209 (accept_3_2 34 156 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 156 209 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 156 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 156 209 (Polychromatic418967fa.accept_7_4_2_6_1_337
  32 156 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 156 209 (accept_3_2 31
  156 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 156 209
  (Polychromatic418967fa.accept_20_10_16_9_1_10927 30 156 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 156 209 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 156 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 156 209 (accept_3_2 28 156 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 156 209 (Polychromatic418967fa.accept_16_11_12_1_1_3001 27 156 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 156 209
  (Polychromatic418967fa.accept_9_8_3_2_1_417 26 156 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 156 209 (accept_3_2 25 156 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 156 209 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 156 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 156 209 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 156 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 156 209 (accept_3_2 22 156 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 156 209 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 156 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 156 209
  (Polychromatic418967fa.accept_15_5_6_14_1_1721 20 156 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 156 209 (accept_3_2 19 156 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 156 209 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 156 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 156 209 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 156 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 156 209 (accept_3_2 16 156 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 156 209 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 156 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 156 209
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 156 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 156 209 (accept_3_2 13 156 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 156 209 (Polychromatic418967fa.accept_21_12_9_20_1_12223 12 156 209 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 11 156 209 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 156 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 156 209 (accept_3_2 10 156 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 156 209 (Polychromatic418967fa.accept_15_9_6_14_1_2627 9 156
  209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 156 209
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 156 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 156 209 (accept_3_2 7 156 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  156 209 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 156 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 156 209 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 156 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 156 209 (accept_3_2 4 156 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 156 209 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 156 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 156 209
  (Polychromatic418967fa.accept_16_2_12_1_1_3086 2 156 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 156 209 (accept_3_2 1 156 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156
  209)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 155 209 (Eq.refl Bool.true)
  (allA_succ_of_accept 54 155 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 155 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 155 209 (Polychromatic418967fa.accept_15_8_5_14_1_986 53 155
  209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 155 209 (accept_3_2 52 155
  209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 155 209
  (Polychromatic418967fa.accept_7_2_1_6_1_173 51 155 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 155 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 155 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 155 209 (accept_3_2 49 155 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 155 209 (Polychromatic418967fa.accept_17_14_2_5_1_3560 48 155 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 155 209
  (Polychromatic418967fa.accept_7_5_1_6_1_163 47 155 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 155 209 (accept_3_2 46 155 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 155 209 (Polychromatic418967fa.accept_20_5_15_9_1_9446 45 155 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 155 209 (Polychromatic418967fa.accept_7_2_1_6_1_173 44 155 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 155 209 (accept_3_2 43 155 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 155 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 155 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 155 209
  (Polychromatic418967fa.accept_10_1_5_9_1_157 41 155 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 155 209 (accept_3_2 40 155 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 155 209 (Polychromatic418967fa.accept_15_9_5_14_1_973 39 155 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 155 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 155 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 155 209 (accept_3_2 37 155 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 155 209 (Polychromatic418967fa.accept_10_6_5_9_1_1233 36 155 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 155 209
  (Polychromatic418967fa.accept_14_7_1_13_1_357 35 155 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 155 209 (accept_3_2 34 155 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 155 209 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 155 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 155 209 (Polychromatic418967fa.accept_15_2_5_14_1_61 32 155 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 155 209 (accept_3_2 31 155 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 155 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 155 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 155 209
  (Polychromatic418967fa.accept_22_7_1_11_1_10719 29 155 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 155 209 (accept_3_2 28 155 209 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 155 209 (Polychromatic418967fa.accept_24_3_11_17_1_10650 27 155 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 155 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 26
  155 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 155 209 (accept_3_2 25
  155 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 155 209
  (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 155 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 155 209 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 155 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 155 209 (accept_3_2 22 155 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 155 209 (Polychromatic418967fa.accept_10_1_5_9_1_157 21 155 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 155 209
  (Polychromatic418967fa.accept_17_3_2_5_1_2556 20 155 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 155 209 (accept_3_2 19 155 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 155 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 155 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 155 209 (Polychromatic418967fa.accept_15_2_5_14_1_61 17 155 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 155 209 (accept_3_2 16 155 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 155 209 (Polychromatic418967fa.accept_13_2_12_1_1_343 15 155
  209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 155 209
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 155 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 155 209 (accept_3_2 13 155 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 155 209 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 155 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 155 209 (Polychromatic418967fa.accept_10_1_5_9_1_157 11 155 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 155 209 (accept_3_2 10 155 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 155 209 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 155 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 155 209
  (Polychromatic418967fa.accept_13_8_12_1_1_4662 8 155 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 155 209 (accept_3_2 7 155 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  155 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 155 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 155 209 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 155 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 155 209 (accept_3_2 4 155 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 155 209 (Polychromatic418967fa.accept_17_3_2_5_1_2556 3 155 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 155 209
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 155 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 155 209 (accept_3_2 1 155 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 155
  209))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 154 209 (Eq.refl Bool.true) (allA_of_3_0 56
  154 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 57 153 209 (Eq.refl Bool.true) (allA_succ_of_accept 56
  153 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 153 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 153 209 (accept_3_2 55 153 209 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 153 209 (Polychromatic418967fa.accept_10_4_3_9_1_1262 54 153 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 153 209 (Polychromatic418967fa.accept_16_5_9_1_1_2070 53 153
  209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 153 209 (accept_3_2 52 153
  209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 153 209
  (Polychromatic418967fa.accept_12_3_9_5_1_853 51 153 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 153 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 153 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 153 209 (accept_3_2 49 153 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 153 209 (Polychromatic418967fa.accept_13_9_10_1_1_1389 48 153 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 153 209
  (Polychromatic418967fa.accept_15_2_3_14_1_972 47 153 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 153 209 (accept_3_2 46 153 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 153 209 (Polychromatic418967fa.accept_16_13_9_1_1_3022 45 153 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 153 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 153 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 153 209 (accept_3_2 43 153 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 153 209 (Polychromatic418967fa.accept_16_10_9_1_1_9973 42 153 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 153 209
  (Polychromatic418967fa.accept_15_11_3_14_1_971 41 153 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 153 209 (accept_3_2 40 153 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 153 209 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 153 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 153 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 153 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 153 209 (accept_3_2 37 153 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 153 209 (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 153 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 153 209
  (Polychromatic418967fa.accept_13_9_10_1_1_1389 35 153 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 153 209 (accept_3_2 34 153 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 153 209 (Polychromatic418967fa.accept_18_15_9_11_1_4371 33 153 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 153 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 153 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 153 209 (accept_3_2 31 153 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 153 209 (Polychromatic418967fa.accept_13_4_10_1_1_1390 30 153 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 153 209
  (Polychromatic418967fa.accept_16_13_9_1_1_3022 29 153 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 153 209 (accept_3_2 28 153 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 153 209 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 153 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 153 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 153 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 153 209 (accept_3_2 25 153 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 153 209 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 153 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 153 209
  (Polychromatic418967fa.accept_21_2_6_20_1_6059 23 153 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 153 209 (accept_3_2 22 153 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 153 209 (Polychromatic418967fa.accept_16_5_9_1_1_2070 21 153 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 153 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 153 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 209 (accept_3_2 19 153 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 153 209 (Polychromatic418967fa.accept_16_2_9_1_1_6404 18 153 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 153 209
  (Polychromatic418967fa.accept_13_4_10_1_1_1390 17 153 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 153 209 (accept_3_2 16 153 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 153 209 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 153 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 153 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 153 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 209 (accept_3_2 13 153 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 153 209 (Polychromatic418967fa.accept_18_12_9_11_1_4370 12 153 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 153 209
  (Polychromatic418967fa.accept_13_11_10_1_1_1409 11 153 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 153 209 (accept_3_2 10 153 209 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 153 209 (Polychromatic418967fa.accept_13_9_10_1_1_1389 9 153 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 153 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 153 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 209 (accept_3_2 7 153 209
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 153 209 (Polychromatic418967fa.accept_10_6_3_9_1_1207
  6 153 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 153 209
  (Polychromatic418967fa.accept_16_5_9_1_1_2070 5 153 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 153 209 (accept_3_2 4 153 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  153 209 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 153 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 153 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 153 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 209 (accept_3_2 1 153 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 153 209))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 152 209
  (Eq.refl Bool.true) (allA_succ_of_gcd 57 152 209 19 3 8 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 56 152 209 (Polychromatic418967fa.accept_21_14_5_20_1_12299 56 152 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 152 209 (accept_3_2 55 152 209
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 152 209 (Polychromatic418967fa.accept_13_2_9_1_1_67
  54 152 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 152 209
  (Polychromatic418967fa.accept_7_4_5_6_1_344 53 152 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 152 209 (accept_3_2 52 152 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 152 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 152 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 152 209 (Polychromatic418967fa.accept_7_1_5_6_1_59 50 152 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 152 209 (accept_3_2 49 152 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 152 209 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 152 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 152 209
  (Polychromatic418967fa.accept_10_7_2_9_1_775 47 152 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 152 209 (accept_3_2 46 152 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 152 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 152 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 152 209 (Polychromatic418967fa.accept_13_5_9_1_1_1405 44 152 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 152 209 (accept_3_2 43 152 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 152 209 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 152 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 152 209
  (Polychromatic418967fa.accept_9_5_8_2_1_409 41 152 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 152 209 (accept_3_2 40 152 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 152 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 152 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 152 209 19 2 8 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 152 209 (accept_3_2 37 152 209 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 152 209 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 152 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 152 209 (Polychromatic418967fa.accept_15_5_2_14_1_1693 35 152
  209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 152 209 (accept_3_2 34 152
  209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 152 209
  (Polychromatic418967fa.accept_6_3_2_5_1_32 33 152 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 152 209 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 152 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 152 209 (accept_3_2 31 152 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 152 209 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 152 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 152 209 (Polychromatic418967fa.accept_7_1_5_6_1_59 29
  152 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 152 209 (accept_3_2 28
  152 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 152 209
  (Polychromatic418967fa.accept_6_3_2_5_1_32 27 152 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 152 209 (Polychromatic418967fa.accept_12_2_8_5_1_408 26 152 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 152 209 (accept_3_2 25 152 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 152 209 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 152 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 152 209 (Polychromatic418967fa.accept_9_5_8_2_1_409
  23 152 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 152 209 (accept_3_2 22
  152 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 152 209
  (Polychromatic418967fa.accept_6_3_2_5_1_32 21 152 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 152 209 (Polychromatic418967fa.accept_14_6_12_13_1_3180 20 152 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 19 152 209 19 1 8 11 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 18 152 209
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 152 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 152 209 (Polychromatic418967fa.accept_10_7_2_9_1_775 17 152 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 152 209 (accept_3_2 16 152 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 152 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 152 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 152 209 (Polychromatic418967fa.accept_9_5_8_2_1_409
  14 152 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 152 209 (accept_3_2 13
  152 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 152 209
  (Polychromatic418967fa.accept_9_3_8_2_1_162 12 152 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 152 209 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 152 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 152 209 (accept_3_2 10 152 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 152 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 152 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 152 209 (Polychromatic418967fa.accept_7_1_5_6_1_59 8
  152 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 152 209 (accept_3_2 7 152
  209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 152 209
  (Polychromatic418967fa.accept_9_6_8_2_1_410 6 152 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 152 209 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 152 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 152 209 (accept_3_2 4 152 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 152 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 152 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 152 209 (Polychromatic418967fa.accept_12_2_8_5_1_408 2
  152 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 152 209 (accept_3_2 1 152
  209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152
  209)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 151 209 (Eq.refl Bool.true) (allA_of_3_0
  59 151 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 150 209 (Eq.refl Bool.true) (allA_succ_of_accept 59
  150 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 150 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 150 209 (accept_3_2 58 150 209 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 150 209 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 150 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 150 209 (Polychromatic418967fa.accept_20_16_10_9_1_9431 56 150
  209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 150 209 (accept_3_2 55 150
  209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 150 209
  (Polychromatic418967fa.accept_21_12_3_20_1_4567 54 150 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 150 209 (Polychromatic418967fa.accept_7_4_3_6_1_340 53 150 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 150 209 (accept_3_2 52 150 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 150 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 150 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 150 209
  (Polychromatic418967fa.accept_9_5_6_2_1_161 50 150 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 150 209 (accept_3_2 49 150 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 150 209 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 150 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 150 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 150 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 150 209 (accept_3_2 46 150 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 150 209 (Polychromatic418967fa.accept_13_6_7_1_1_335 45 150 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 150 209
  (Polychromatic418967fa.accept_7_2_3_6_1_4 44 150 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 150 209 (accept_3_2 43 150 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 150 209 (Polychromatic418967fa.accept_13_3_7_1_1_334 42 150 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 150 209 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 150 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 150 209 (accept_3_2 40 150 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 150 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 150 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 150 209
  (Polychromatic418967fa.accept_21_17_3_20_1_6054 38 150 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 150 209 (accept_3_2 37 150 209 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 150 209 (Polychromatic418967fa.accept_17_2_14_5_1_2575 36 150 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 150 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 150 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 150 209 (accept_3_2 34 150 209
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 150 209
  (Polychromatic418967fa.accept_18_15_6_11_1_5651 33 150 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 150 209 (Polychromatic418967fa.accept_7_4_3_6_1_340 32 150 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 150 209 (accept_3_2 31 150 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 150 209 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 150 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 150 209
  (Polychromatic418967fa.accept_13_3_7_1_1_334 29 150 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 150 209 (accept_3_2 28 150 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 150 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 150 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 150 209 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 150 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 150 209 (accept_3_2 25 150 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 150 209 (Polychromatic418967fa.accept_13_11_7_1_1_1386 24 150 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 150 209
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 150 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 150 209 (accept_3_2 22 150 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 150 209 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 150 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 150 209 (Polychromatic418967fa.accept_28_20_10_13_1_12310 20 150 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 150 209 (accept_3_2 19 150 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 150 209 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 150 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 150 209
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 150 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 150 209 (accept_3_2 16 150 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 150 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 150 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 150 209 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 150 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 150 209 (accept_3_2 13 150 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 150 209 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 150 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 150 209
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 150 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 150 209 (accept_3_2 10 150 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  150 209 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 150 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 150 209 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 150 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 150 209 (accept_3_2 7 150 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 150 209 (Polychromatic418967fa.accept_13_6_7_1_1_335 6 150 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 150 209
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 150 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 150 209 (accept_3_2 4 150 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  150 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 150 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 150 209 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 150 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 150 209 (accept_3_2 1 150 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 150 209)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 149
  209 (Eq.refl Bool.true) (allA_succ_of_accept 60 149 209 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 149 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 149 209
  (Polychromatic418967fa.accept_7_3_2_6_1_56 59 149 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 149 209 (accept_3_2 58 149 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 149 209 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 149 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 149 209 (Polychromatic418967fa.accept_21_14_2_20_1_12297 56 149 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 149 209 (accept_3_2 55 149 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 149 209 (Polychromatic418967fa.accept_13_2_6_1_1_3807 54 149
  209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 149 209
  (Polychromatic418967fa.accept_7_4_2_6_1_337 53 149 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 149 209 (accept_3_2 52 149 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 149 209 (Polychromatic418967fa.accept_9_6_5_2_1_421 51 149 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 149 209 (Polychromatic418967fa.accept_7_1_2_6_1_55 50 149 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 149 209 (accept_3_2 49 149 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 149 209 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 149 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 149 209
  (Polychromatic418967fa.accept_13_8_6_1_1_3808 47 149 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 149 209 (accept_3_2 46 149 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 149 209 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 149 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 149 209 (Polychromatic418967fa.accept_8_4_5_1_1_299 44 149 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 149 209 (accept_3_2 43 149 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 149 209 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 149 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 149 209
  (Polychromatic418967fa.accept_13_2_6_1_1_3807 41 149 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 149 209 (accept_3_2 40 149 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 149 209 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 149 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 149 209 (Polychromatic418967fa.accept_7_3_2_6_1_56 38 149 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 149 209 (accept_3_2 37 149 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 149 209 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 149 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 149 209
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 149 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 149 209 (accept_3_2 34 149 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 149 209 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 149 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 149 209 (Polychromatic418967fa.accept_7_4_2_6_1_337 32 149 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 149 209 (accept_3_2 31 149 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 149 209 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 149 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 149 209
  (Polychromatic418967fa.accept_7_1_2_6_1_55 29 149 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 149 209 (accept_3_2 28 149 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 149 209 (Polychromatic418967fa.accept_17_10_13_5_1_3513 27 149 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 149 209 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 149 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 149 209 (accept_3_2 25 149 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 149 209 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 149 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 149 209
  (Polychromatic418967fa.accept_24_23_5_17_1_12309 23 149 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 149 209 (accept_3_2 22 149 209 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 149 209 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 149 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 149 209 (Polychromatic418967fa.accept_8_4_5_1_1_299 20 149 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 149 209 (accept_3_2 19 149 209
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 149 209 (Polychromatic418967fa.accept_7_4_2_6_1_337
  18 149 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 149 209
  (Polychromatic418967fa.accept_7_3_2_6_1_56 17 149 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 149 209 (accept_3_2 16 149 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 149 209 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 149 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 149 209 (Polychromatic418967fa.accept_18_14_5_11_1_5676 14 149 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 149 209 (accept_3_2 13 149 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 149 209 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 149 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 149 209
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 149 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 149 209 (accept_3_2 10 149 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  149 209 (Polychromatic418967fa.accept_13_9_6_1_1_2902 9 149 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 149 209 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 149 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 149 209 (accept_3_2 7 149 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 149 209 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 149 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 149 209
  (Polychromatic418967fa.accept_13_5_6_1_1_822 5 149 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 149 209 (accept_3_2 4 149 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  149 209 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 149 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 149 209 (Polychromatic418967fa.accept_13_2_6_1_1_3807 2 149 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 149 209 (accept_3_2 1 149 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 149 209))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 148
  209 (Eq.refl Bool.true) (allA_of_3_0 62 148 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 63 147 209
  (Eq.refl Bool.true) (allA_succ_of_accept 62 147 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 147 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 147 209 (accept_3_2 61 147 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 147 209 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 147 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 147 209
  (Polychromatic418967fa.accept_9_5_3_2_1_171 59 147 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 147 209 (accept_3_2 58 147 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 147 209 (Polychromatic418967fa.accept_12_9_3_5_1_423 57 147 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 147 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 147 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 147 209 (accept_3_2 55 147 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 147 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 147 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 147 209
  (Polychromatic418967fa.accept_9_8_3_2_1_417 53 147 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 147 209 (accept_3_2 52 147 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 147 209 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 147 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 147 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 147 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 147 209 (accept_3_2 49 147 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 147 209 (Polychromatic418967fa.accept_10_8_7_9_1_425 48 147 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 147 209
  (Polychromatic418967fa.accept_15_2_12_14_1_1709 47 147 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 147 209 (accept_3_2 46 147 209 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 147 209 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 147 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 147 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 147 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 147 209 (accept_3_2 43 147 209
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 147 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 42
  147 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 147 209
  (Polychromatic418967fa.accept_9_5_3_2_1_171 41 147 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 147 209 (accept_3_2 40 147 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 147 209 (Polychromatic418967fa.accept_15_9_12_14_1_963 39 147 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 147 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 147 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 147 209 (accept_3_2 37 147 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 147 209 (Polychromatic418967fa.accept_13_10_4_1_1_2142 36 147 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 147 209
  (Polychromatic418967fa.accept_9_8_3_2_1_417 35 147 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 147 209 (accept_3_2 34 147 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 147 209 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 147 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 147 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 147 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 147 209 (accept_3_2 31 147 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 147 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 147 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 147 209
  (Polychromatic418967fa.accept_13_3_4_1_1_363 29 147 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 147 209 (accept_3_2 28 147 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 147 209 (Polychromatic418967fa.accept_22_5_15_11_1_12238 27 147 209 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 26 147 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 147 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 147 209 (accept_3_2 25 147 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 147 209 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 147 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 147 209
  (Polychromatic418967fa.accept_9_5_3_2_1_171 23 147 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 147 209 (accept_3_2 22 147 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 147 209 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 147 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 147 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 147 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 209 (accept_3_2 19 147 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 147 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 147 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 147 209
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 147 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 147 209 (accept_3_2 16 147 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 147 209 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 147 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 147 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 147 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 147 209 (accept_3_2 13 147 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 147 209 (Polychromatic418967fa.accept_10_2_7_9_1_783 12 147 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 147 209
  (Polychromatic418967fa.accept_15_11_12_14_1_2612 11 147 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 147 209 (accept_3_2 10 147 209 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 147 209 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 147 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 147 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 147 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 209 (accept_3_2 7 147 209
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 147 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 6
  147 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 147 209
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 147 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 147 209 (accept_3_2 4 147 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  147 209 (Polychromatic418967fa.accept_13_3_4_1_1_363 3 147 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 147 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 147 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 209 (accept_3_2 1 147 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 147 209))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64
  146 209 (Eq.refl Bool.true) (allA_succ_of_accept 63 146 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 146 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 146 209
  (Polychromatic418967fa.accept_23_16_8_2_1_9042 62 146 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 146 209 (accept_3_2 61 146 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 146 209 (Polychromatic418967fa.accept_16_12_2_1_1_1215 60 146 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 146 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 146 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 146 209 (accept_3_2 58 146 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 146 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 146 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 146 209
  (Polychromatic418967fa.accept_12_8_2_5_1_844 56 146 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 146 209 (accept_3_2 55 146 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 146 209 (Polychromatic418967fa.accept_13_2_3_1_1_3823 54 146 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 146 209 (Polychromatic418967fa.accept_10_3_6_9_1_779 53 146 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 146 209 (accept_3_2 52 146 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 146 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 146 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 146 209
  (Polychromatic418967fa.accept_13_11_3_1_1_1397 50 146 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 146 209 (accept_3_2 49 146 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 146 209 (Polychromatic418967fa.accept_15_3_11_14_1_1705 48 146 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 146 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 146 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 146 209 (accept_3_2 46 146 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 146 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 146 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 146 209
  (Polychromatic418967fa.accept_12_8_2_5_1_844 44 146 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 146 209 (accept_3_2 43 146 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 146 209 (Polychromatic418967fa.accept_15_12_11_14_1_3464 42 146 209 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 41 146 209 (Polychromatic418967fa.accept_13_2_3_1_1_3823 41 146 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 146 209 (accept_3_2 40 146 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 146 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 146 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 146 209
  (Polychromatic418967fa.accept_16_6_2_1_1_4081 38 146 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 146 209 (accept_3_2 37 146 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 146 209 (Polychromatic418967fa.accept_25_11_21_9_1_12308 36 146 209 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 35 146 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 146 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 146 209 (accept_3_2 34 146 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 146 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 146 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 146 209
  (Polychromatic418967fa.accept_12_8_2_5_1_844 32 146 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 146 209 (accept_3_2 31 146 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 146 209 (Polychromatic418967fa.accept_13_4_3_1_1_2898 30 146 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 146 209 (Polychromatic418967fa.accept_17_12_10_5_1_4756 29 146 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 146 209 (accept_3_2 28 146 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 146 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 146 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 146 209
  (Polychromatic418967fa.accept_14_12_6_13_1_3173 26 146 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 146 209 (accept_3_2 25 146 209 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 146 209 (Polychromatic418967fa.accept_13_11_3_1_1_1397 24 146 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 146 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 146 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 146 209 (accept_3_2 22 146 209
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 146 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 21
  146 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 146 209
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 146 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 146 209 (accept_3_2 19 146 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 146 209 (Polychromatic418967fa.accept_13_5_3_1_1_1398 18 146 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 146 209 (Polychromatic418967fa.accept_13_4_3_1_1_2898 17 146 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 146 209 (accept_3_2 16 146 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 146 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 146 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 146 209
  (Polychromatic418967fa.accept_17_14_10_5_1_8628 14 146 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 146 209 (accept_3_2 13 146 209 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 146 209 (Polychromatic418967fa.accept_14_12_6_13_1_3173 12 146 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 146 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 11
  146 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 146 209 (accept_3_2 10
  146 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 146 209
  (Polychromatic418967fa.accept_6_3_2_5_1_32 9 146 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 146 209 (Polychromatic418967fa.accept_12_8_2_5_1_844 8 146 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 146 209 (accept_3_2 7 146 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 146 209 (Polychromatic418967fa.accept_13_6_3_1_1_1413 6 146 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 146 209 (Polychromatic418967fa.accept_10_5_6_9_1_2235
  5 146 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 146 209 (accept_3_2 4
  146 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 146 209
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 146 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 146 209 (Polychromatic418967fa.accept_13_2_3_1_1_3823 2 146 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 146 209 (accept_3_2 1 146 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 146 209)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 145 209
  (Eq.refl Bool.true) (allA_of_3_0 65 145 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 66 144 209 (Eq.refl
  Bool.true) (allA_succ_of_accept 65 144 209 (Polychromatic418967fa.accept_7_2_4_6_1_166 65 144 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 144 209 (accept_3_2 64 144 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 144 209 (Polychromatic418967fa.accept_10_3_4_9_1_15 63 144 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 144 209
  (Polychromatic418967fa.accept_20_2_4_9_1_9524 62 144 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 144 209 (accept_3_2 61 144 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 144 209 (Polychromatic418967fa.accept_25_10_19_9_1_8739 60 144 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 144 209 (Polychromatic418967fa.accept_7_3_4_6_1_329 59 144 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 144 209 (accept_3_2 58 144 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 144 209 (Polychromatic418967fa.accept_15_12_9_14_1_2635 57 144 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 144 209
  (Polychromatic418967fa.accept_21_14_18_20_1_12307 56 144 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 144 209 (accept_3_2 55 144 209 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 144 209 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 144 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 144 209 (Polychromatic418967fa.accept_10_3_4_9_1_15 53 144 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 144 209 (accept_3_2 52 144 209
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 144 209 (Polychromatic418967fa.accept_7_2_4_6_1_166
  51 144 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 144 209
  (Polychromatic418967fa.accept_15_5_9_14_1_1724 50 144 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 144 209 (accept_3_2 49 144 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 144 209 (Polychromatic418967fa.accept_10_8_4_9_1_1229 48 144 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 144 209 (Polychromatic418967fa.accept_7_5_4_6_1_167 47 144 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 144 209 (accept_3_2 46 144 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 144 209 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 144 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 144 209
  (Polychromatic418967fa.accept_7_2_4_6_1_166 44 144 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 144 209 (accept_3_2 43 144 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 144 209 (Polychromatic418967fa.accept_15_12_9_14_1_2635 42 144 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 144 209 (Polychromatic418967fa.accept_22_19_12_11_1_12306 41 144 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 144 209 (accept_3_2 40 144 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 144 209 (Polychromatic418967fa.accept_20_19_4_9_1_5025 39 144
  209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 144 209
  (Polychromatic418967fa.accept_7_3_4_6_1_329 38 144 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 144 209 (accept_3_2 37 144 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 144 209 (Polychromatic418967fa.accept_15_6_9_14_1_3457 36 144 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 144 209 (Polychromatic418967fa.accept_10_5_4_9_1_420 35 144 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 144 209 (accept_3_2 34 144 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 144 209 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 144 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 144 209
  (Polychromatic418967fa.accept_21_11_18_20_1_1877 32 144 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 144 209 (accept_3_2 31 144 209 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 144 209 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 144 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 144 209 (Polychromatic418967fa.accept_17_12_8_5_1_6018 29 144
  209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 144 209 (accept_3_2 28 144
  209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 144 209
  (Polychromatic418967fa.accept_15_12_9_14_1_2635 27 144 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 144 209 (Polychromatic418967fa.accept_7_5_4_6_1_167 26 144 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 144 209 (accept_3_2 25 144 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 144 209 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 144 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 144 209
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 144 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 144 209 (accept_3_2 22 144 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 144 209 (Polychromatic418967fa.accept_15_6_9_14_1_3457 21 144 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 144 209 (Polychromatic418967fa.accept_15_5_9_14_1_1724 20 144 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 144 209 (accept_3_2 19 144 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 144 209 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 144
  209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 144 209
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 144 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 144 209 (accept_3_2 16 144 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 144 209 (Polychromatic418967fa.accept_10_5_4_9_1_420 15 144 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 144 209 (Polychromatic418967fa.accept_20_14_4_9_1_2249 14 144 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 144 209 (accept_3_2 13 144 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 144 209 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 144 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 144 209
  (Polychromatic418967fa.accept_21_11_18_20_1_1877 11 144 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 144 209 (accept_3_2 10 144 209 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 144 209 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 144 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 144 209 (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 144 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 144 209 (accept_3_2 7 144 209
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 144 209 (Polychromatic418967fa.accept_15_6_9_14_1_3457
  6 144 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 144 209
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 144 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 144 209 (accept_3_2 4 144 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  144 209 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 144 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 144 209 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 144 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 144 209 (accept_3_2 1 144 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 144 209)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  67 143 209 (Eq.refl Bool.true) (allA_succ_of_gcd 66 143 209 11 6 13 19 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 143 209 (Polychromatic418967fa.accept_7_2_3_6_1_4 65
  143 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 143 209 (accept_3_2 64
  143 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 143 209
  (Polychromatic418967fa.accept_17_12_7_5_1_8659 63 143 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 143 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 143 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 143 209 (accept_3_2 61 143 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 143 209 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 143 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 143 209 (Polychromatic418967fa.accept_9_5_8_2_1_409
  59 143 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 143 209 (accept_3_2 58
  143 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 143 209
  (Polychromatic418967fa.accept_9_3_8_2_1_162 57 143 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 143 209 (Polychromatic418967fa.accept_10_6_3_9_1_1207 56 143 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 143 209 11 5 13 19 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 143 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 54
  143 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 143 209
  (Polychromatic418967fa.accept_7_4_3_6_1_340 53 143 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 143 209 (accept_3_2 52 143 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 143 209 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 143 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 143 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 143 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 143 209 (accept_3_2 49 143 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 143 209 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 143 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 143 209
  (Polychromatic418967fa.accept_31_16_19_23_1_1442 47 143 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 143 209 (accept_3_2 46 143 209 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 143 209 (Polychromatic418967fa.accept_17_11_7_5_1_1567 45 143 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 143 209 11 4 13 19 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 143 209 (accept_3_2 43 143 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 143 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 143 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 143 209
  (Polychromatic418967fa.accept_9_5_8_2_1_409 41 143 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 143 209 (accept_3_2 40 143 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 143 209 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 143 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 143 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 143 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 143 209 (accept_3_2 37 143 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 143 209 (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 143 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 143 209
  (Polychromatic418967fa.accept_15_5_8_14_1_432 35 143 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 143 209 (accept_3_2 34 143 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33
  143 209 11 3 13 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 143 209 (Polychromatic418967fa.accept_7_4_3_6_1_340 32 143 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 143 209 (accept_3_2 31 143 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 143 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 143 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 143 209
  (Polychromatic418967fa.accept_17_12_7_5_1_8659 29 143 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 143 209 (accept_3_2 28 143 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 143 209 (Polychromatic418967fa.accept_16_11_15_1_1_2074 27 143 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 143 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 143 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 143 209 (accept_3_2 25 143 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 143 209 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 143 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 143 209
  (Polychromatic418967fa.accept_7_2_3_6_1_4 23 143 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 143 209 11 2 13 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 143 209 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 143 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 143 209 (Polychromatic418967fa.accept_15_5_8_14_1_432
  20 143 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 143 209 (accept_3_2 19
  143 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 143 209
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 143 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 143 209 (Polychromatic418967fa.accept_26_17_13_1_1_12305 17 143 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 143 209 (accept_3_2 16 143 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 143 209 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 143 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 143 209
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 143 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 143 209 (accept_3_2 13 143 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 143 209 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 143 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 11 143 209 11 1 13 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 10 143 209 (accept_3_2 10 143 209 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 143 209 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 143 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 143 209 (Polychromatic418967fa.accept_16_8_15_1_1_3006 8 143
  209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 143 209 (accept_3_2 7 143 209
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 143 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 6
  143 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 143 209
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 143 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 143 209 (accept_3_2 4 143 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  143 209 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 143 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 143 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 143 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 143 209 (accept_3_2 1 143 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 143 209))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  68 142 209 (Eq.refl Bool.true) (allA_of_3_0 68 142 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 69 141 209
  (Eq.refl Bool.true) (allA_succ_of_accept 68 141 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 141 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 141 209 (accept_3_2 67 141 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 141 209 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 141 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 141 209
  (Polychromatic418967fa.accept_7_2_1_6_1_173 65 141 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 141 209 (accept_3_2 64 141 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 141 209 (Polychromatic418967fa.accept_12_3_9_5_1_853 63 141 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 141 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 141 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 141 209 (accept_3_2 61 141 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 141 209 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 141 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 141 209
  (Polychromatic418967fa.accept_9_5_6_2_1_161 59 141 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 141 209 (accept_3_2 58 141 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 141 209 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 141 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 141 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 141 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 141 209 (accept_3_2 55 141 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 141 209 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 141 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 141 209
  (Polychromatic418967fa.accept_9_8_6_2_1_744 53 141 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 141 209 (accept_3_2 52 141 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 141 209 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 141 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 141 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 141 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 141 209 (accept_3_2 49 141 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 141 209 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 141 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 141 209
  (Polychromatic418967fa.accept_7_5_1_6_1_163 47 141 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 141 209 (accept_3_2 46 141 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 141 209 (Polychromatic418967fa.accept_10_5_1_9_1_791 45 141 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 141 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 141 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 141 209 (accept_3_2 43 141 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 141 209 (Polychromatic418967fa.accept_10_2_1_9_1_1248 42 141 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 141 209
  (Polychromatic418967fa.accept_9_5_6_2_1_161 41 141 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 141 209 (accept_3_2 40 141 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 141 209 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 141 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 141 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 141 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 141 209 (accept_3_2 37 141 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 141 209 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 141 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 141 209
  (Polychromatic418967fa.accept_9_8_6_2_1_744 35 141 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 141 209 (accept_3_2 34 141 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 141 209 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 141 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 141 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 141 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 141 209 (accept_3_2 31 141 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 141 209 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 141 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 141 209
  (Polychromatic418967fa.accept_13_3_11_1_1_2122 29 141 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 141 209 (accept_3_2 28 141 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 141 209 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 141 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 141 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 141 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 209 (accept_3_2 25 141 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 141 209 (Polychromatic418967fa.accept_15_9_6_14_1_2627 24 141 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 141 209
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 141 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 141 209 (accept_3_2 22 141 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 141 209 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 141 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 141 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 141 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 141 209 (accept_3_2 19 141 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 141 209 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 141 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 141 209
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 141 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 141 209 (accept_3_2 16 141 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 141 209 (Polychromatic418967fa.accept_10_5_1_9_1_791 15 141 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 141 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 141 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 209 (accept_3_2 13 141 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 141 209 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 141 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 141 209
  (Polychromatic418967fa.accept_27_11_6_20_1_12304 11 141 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 141 209 (accept_3_2 10 141 209 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 141 209 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 141 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 141 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 141 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 209 (accept_3_2 7 141 209
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 141 209
  (Polychromatic418967fa.accept_18_6_15_11_1_3141 6 141 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 141 209 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 141 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 209 (accept_3_2 4 141 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 141 209 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 141 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 141 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 2
  141 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 209 (accept_3_2 1 141
  209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 141
  209))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 140 209 (Eq.refl Bool.true)
  (allA_succ_of_accept 69 140 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 140 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 140 209 (Polychromatic418967fa.accept_15_8_5_14_1_986 68 140
  209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 140 209 (accept_3_2 67 140
  209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 140 209
  (Polychromatic418967fa.accept_9_3_5_2_1_28 66 140 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 140 209 (Polychromatic418967fa.accept_21_2_14_20_1_841 65 140 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 140 209 (accept_3_2 64 140 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 140 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 140 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 140 209 (Polychromatic418967fa.accept_9_8_5_2_1_422
  62 140 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 140 209 (accept_3_2 61
  140 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 140 209
  (Polychromatic418967fa.accept_9_6_5_2_1_421 60 140 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 140 209 (Polychromatic418967fa.accept_16_11_12_1_1_3001 59 140 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 140 209 (accept_3_2 58 140 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 140 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 140 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 140 209
  (Polychromatic418967fa.accept_13_4_10_1_1_1390 56 140 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 140 209 (accept_3_2 55 140 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 140 209 (Polychromatic418967fa.accept_15_9_5_14_1_973 54 140 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 140 209 (Polychromatic418967fa.accept_8_5_4_1_1_111 53 140 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 140 209 (accept_3_2 52 140 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 140 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 140 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 140 209
  (Polychromatic418967fa.accept_12_2_8_5_1_408 50 140 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 140 209 (accept_3_2 49 140 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 140 209 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 140 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 140 209 (Polychromatic418967fa.accept_15_2_5_14_1_61 47 140 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 140 209 (accept_3_2 46 140 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 140 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 140 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 140 209
  (Polychromatic418967fa.accept_9_8_5_2_1_422 44 140 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 140 209 (accept_3_2 43 140 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 140 209 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 140 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 140 209 (Polychromatic418967fa.accept_18_5_14_11_1_2073 41 140 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 140 209 (accept_3_2 40 140 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 140 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 140 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 140 209
  (Polychromatic418967fa.accept_12_2_8_5_1_408 38 140 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 140 209 (accept_3_2 37 140 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 140 209 (Polychromatic418967fa.accept_15_6_5_14_1_429 36 140 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 140 209 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 140 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 140 209 (accept_3_2 34 140 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 140 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 140 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 140 209
  (Polychromatic418967fa.accept_15_2_5_14_1_61 32 140 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 140 209 (accept_3_2 31 140 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 140 209 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 140 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 140 209 (Polychromatic418967fa.accept_8_5_4_1_1_111 29 140 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 140 209 (accept_3_2 28 140 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 140 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 140 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 140 209
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 140 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 140 209 (accept_3_2 25 140 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 140 209 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 140 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 140 209 (Polychromatic418967fa.accept_15_8_5_14_1_986 23 140 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 140 209 (accept_3_2 22 140 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 140 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 140 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 140 209
  (Polychromatic418967fa.accept_16_4_12_1_1_1204 20 140 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 140 209 (accept_3_2 19 140 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 140 209 (Polychromatic418967fa.accept_16_2_12_1_1_3086 18 140 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 140 209 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 140 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 140 209 (accept_3_2 16 140 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 140 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 140 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 140 209
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 140 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 140 209 (accept_3_2 13 140 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 140 209 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 140 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 140 209 (Polychromatic418967fa.accept_13_11_10_1_1_1409 11 140 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 140 209 (accept_3_2 10 140 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 140 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 140 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 140 209
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 140 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 140 209 (accept_3_2 7 140 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  140 209 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 140 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 140 209 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 140 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 140 209 (accept_3_2 4 140 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 140 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 140 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 140 209
  (Polychromatic418967fa.accept_12_2_8_5_1_408 2 140 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 140 209 (accept_3_2 1 140 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140
  209)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 139 209 (Eq.refl Bool.true)
  (allA_of_3_0 71 139 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 72 138 209 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 138 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 138 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 138 209 (accept_3_2 70 138 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 138 209 (Polychromatic418967fa.accept_9_6_3_2_1_431 69 138 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 138 209 (Polychromatic418967fa.accept_9_5_3_2_1_171
  68 138 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 138 209 (accept_3_2 67
  138 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 138 209
  (Polychromatic418967fa.accept_21_3_12_20_1_1891 66 138 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 138 209 (Polychromatic418967fa.accept_17_14_2_5_1_3560 65 138 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 138 209 (accept_3_2 64 138 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 138 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 138 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 138 209
  (Polychromatic418967fa.accept_9_8_3_2_1_417 62 138 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 138 209 (accept_3_2 61 138 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 138 209 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 138 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 138 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 138 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 138 209 (accept_3_2 58 138 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 138 209 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 138 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 138 209
  (Polychromatic418967fa.accept_15_11_3_14_1_971 56 138 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 138 209 (accept_3_2 55 138 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 138 209 (Polychromatic418967fa.accept_10_4_8_9_1_784 54 138 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 138 209 (Polychromatic418967fa.accept_7_4_5_6_1_344 53 138 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 138 209 (accept_3_2 52 138 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 138 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 138 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 138 209
  (Polychromatic418967fa.accept_7_1_5_6_1_59 50 138 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 138 209 (accept_3_2 49 138 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 138 209 (Polychromatic418967fa.accept_13_9_8_1_1_824 48 138 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 138 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 138 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 138 209 (accept_3_2 46 138 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 138 209 (Polychromatic418967fa.accept_13_6_8_1_1_2913 45 138 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 138 209
  (Polychromatic418967fa.accept_9_8_3_2_1_417 44 138 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 138 209 (accept_3_2 43 138 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 138 209 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 138 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 138 209 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 138 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 138 209 (accept_3_2 40 138 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 138 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 138 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 138 209
  (Polychromatic418967fa.accept_13_12_8_1_1_825 38 138 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 138 209 (accept_3_2 37 138 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 138 209 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 138 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 138 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 138 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 138 209 (accept_3_2 34 138 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 138 209 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 138 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 138 209
  (Polychromatic418967fa.accept_7_4_5_6_1_344 32 138 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 138 209 (accept_3_2 31 138 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 138 209 (Polychromatic418967fa.accept_21_9_12_20_1_10792 30 138 209 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 29 138 209 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 138 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 138 209 (accept_3_2 28 138 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 138 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 138 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 138 209
  (Polychromatic418967fa.accept_9_8_3_2_1_417 26 138 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 138 209 (accept_3_2 25 138 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 138 209 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 138 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 138 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 138 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 138 209 (accept_3_2 22 138 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 138 209 (Polychromatic418967fa.accept_10_1_8_9_1_787 21 138 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 138 209
  (Polychromatic418967fa.accept_13_7_8_1_1_2145 20 138 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 138 209 (accept_3_2 19 138 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 138 209 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 138 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 138 209 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 138 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 138 209 (accept_3_2 16 138 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 138 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 138 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 138 209
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 138 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 138 209 (accept_3_2 13 138 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 138 209 (Polychromatic418967fa.accept_13_12_8_1_1_825 12 138 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 138 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 138 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 138 209 (accept_3_2 10 138 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 138 209 (Polychromatic418967fa.accept_13_9_8_1_1_824 9 138 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 138 209
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 138 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 138 209 (accept_3_2 7 138 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  138 209 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 138 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 138 209 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 138 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 138 209 (accept_3_2 4 138 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 138 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 138 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 138 209
  (Polychromatic418967fa.accept_15_2_3_14_1_972 2 138 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 138 209 (accept_3_2 1 138 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  209)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 137 209 (Eq.refl Bool.true)
  (allA_succ_of_accept 72 137 209 (Polychromatic418967fa.accept_7_2_4_6_1_166 72 137 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 137 209 (Polychromatic418967fa.accept_13_6_7_1_1_335 71 137
  209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 137 209 (accept_3_2 70 137
  209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 137 209
  (Polychromatic418967fa.accept_16_5_9_1_1_2070 69 137 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 137 209 (Polychromatic418967fa.accept_7_5_4_6_1_167 68 137 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 137 209 (accept_3_2 67 137 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 137 209 (Polychromatic418967fa.accept_7_3_4_6_1_329 66 137 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 137 209 (Polychromatic418967fa.accept_7_2_4_6_1_166
  65 137 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 137 209 (accept_3_2 64
  137 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 137 209
  (Polychromatic418967fa.accept_13_11_7_1_1_1386 63 137 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 137 209 (Polychromatic418967fa.accept_10_2_7_9_1_783 62 137 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 137 209 (accept_3_2 61 137 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 137 209 (Polychromatic418967fa.accept_13_8_7_1_1_1385 60 137 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 137 209
  (Polychromatic418967fa.accept_7_3_4_6_1_329 59 137 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 137 209 (accept_3_2 58 137 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 137 209 (Polychromatic418967fa.accept_15_12_2_14_1_5659 57 137 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 137 209 (Polychromatic418967fa.accept_16_8_9_1_1_7753 56 137 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 137 209 (accept_3_2 55 137 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 137 209 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 137 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 137 209
  (Polychromatic418967fa.accept_16_5_9_1_1_2070 53 137 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 137 209 (accept_3_2 52 137 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 137 209 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 137 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 137 209 (Polychromatic418967fa.accept_13_11_7_1_1_1386 50 137 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 137 209 (accept_3_2 49 137 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 137 209 (Polychromatic418967fa.accept_10_8_7_9_1_425 48 137
  209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 137 209
  (Polychromatic418967fa.accept_7_5_4_6_1_167 47 137 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 137 209 (accept_3_2 46 137 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 137 209 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 137 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 137 209 (Polychromatic418967fa.accept_7_2_4_6_1_166 44 137 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 137 209 (accept_3_2 43 137 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 137 209 (Polychromatic418967fa.accept_10_2_7_9_1_783 42 137 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 137 209
  (Polychromatic418967fa.accept_27_14_2_20_1_12303 41 137 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 137 209 (accept_3_2 40 137 209 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 137 209 (Polychromatic418967fa.accept_21_18_11_20_1_3154 39 137 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 137 209 (Polychromatic418967fa.accept_7_3_4_6_1_329
  38 137 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 137 209 (accept_3_2 37
  137 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 137 209
  (Polychromatic418967fa.accept_27_9_2_20_1_12263 36 137 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 137 209 (Polychromatic418967fa.accept_15_5_2_14_1_1693 35 137 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 137 209 (accept_3_2 34 137 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 137 209 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 137 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 137 209
  (Polychromatic418967fa.accept_10_2_7_9_1_783 32 137 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 137 209 (accept_3_2 31 137 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 137 209 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 137 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 137 209 (Polychromatic418967fa.accept_13_3_7_1_1_334 29 137 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 137 209 (accept_3_2 28 137 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 137 209 (Polychromatic418967fa.accept_15_12_2_14_1_5659 27 137
  209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 137 209
  (Polychromatic418967fa.accept_7_5_4_6_1_167 26 137 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 137 209 (accept_3_2 25 137 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 137 209 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 137 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 137 209 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 137 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 137 209 (accept_3_2 22 137 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 137 209 (Polychromatic418967fa.accept_13_8_7_1_1_1385 21 137 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 137 209
  (Polychromatic418967fa.accept_15_5_2_14_1_1693 20 137 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 137 209 (accept_3_2 19 137 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 137 209 (Polychromatic418967fa.accept_10_8_7_9_1_425 18 137 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 137 209 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 137 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 137 209 (accept_3_2 16 137 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 137 209 (Polychromatic418967fa.accept_22_15_5_11_1_12302 15 137 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 137 209
  (Polychromatic418967fa.accept_21_14_11_20_1_12301 14 137 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 137 209 (accept_3_2 13 137 209 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 137 209 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 137 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 137 209 (Polychromatic418967fa.accept_13_11_7_1_1_1386 11 137
  209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 137 209 (accept_3_2 10 137
  209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 137 209
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 137 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 137 209 (Polychromatic418967fa.accept_10_8_7_9_1_425 8 137 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 137 209 (accept_3_2 7 137 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 137 209 (Polychromatic418967fa.accept_13_6_7_1_1_335 6 137 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 137 209 (Polychromatic418967fa.accept_7_5_4_6_1_167 5
  137 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 209 (accept_3_2 4 137
  209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 137 209
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 137 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 137 209 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 137 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 137 209 (accept_3_2 1 137 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 137 209))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74
  136 209 (Eq.refl Bool.true) (allA_of_3_0 74 136 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 75 135 209
  (Eq.refl Bool.true) (allA_succ_of_accept 74 135 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 135 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 135 209 (accept_3_2 73 135 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 135 209 (Polychromatic418967fa.accept_16_8_7_1_1_8875 72 135
  209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 135 209
  (Polychromatic418967fa.accept_7_1_2_6_1_55 71 135 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 135 209 (accept_3_2 70 135 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 135 209 (Polychromatic418967fa.accept_12_9_3_5_1_423 69 135 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 135 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 135 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 135 209 (accept_3_2 67 135 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 135 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 135 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 135 209
  (Polychromatic418967fa.accept_20_5_15_9_1_9446 65 135 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 135 209 (accept_3_2 64 135 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 135 209 (Polychromatic418967fa.accept_20_3_15_9_1_6456 63 135 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 135 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 135 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 135 209 (accept_3_2 61 135 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 135 209 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 135 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 135 209
  (Polychromatic418967fa.accept_7_3_2_6_1_56 59 135 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 135 209 (accept_3_2 58 135 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 135 209 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 135 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 135 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 135 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 135 209 (accept_3_2 55 135 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 135 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 135 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 135 209
  (Polychromatic418967fa.accept_7_4_2_6_1_337 53 135 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 135 209 (accept_3_2 52 135 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 135 209 (Polychromatic418967fa.accept_10_1_5_9_1_157 51 135 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 135 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 135 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 135 209 (accept_3_2 49 135 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 135 209 (Polychromatic418967fa.accept_13_9_5_1_1_1382 48 135 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 135 209
  (Polychromatic418967fa.accept_13_8_5_1_1_1381 47 135 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 135 209 (accept_3_2 46 135 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 135 209 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 135 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 135 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 135 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 135 209 (accept_3_2 43 135 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 135 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 135 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 135 209
  (Polychromatic418967fa.accept_10_1_5_9_1_157 41 135 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 135 209 (accept_3_2 40 135 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 135 209 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 135 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 135 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 135 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 135 209 (accept_3_2 37 135 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 135 209 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 135 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 135 209
  (Polychromatic418967fa.accept_13_9_5_1_1_1382 35 135 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 135 209 (accept_3_2 34 135 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 135 209 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 135 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 135 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 135 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 135 209 (accept_3_2 31 135 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 135 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 135 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 135 209
  (Polychromatic418967fa.accept_7_1_2_6_1_55 29 135 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 135 209 (accept_3_2 28 135 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 135 209 (Polychromatic418967fa.accept_21_6_9_20_1_3190 27 135 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 135 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 135 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 135 209 (accept_3_2 25 135 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 135 209 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 135 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 135 209
  (Polychromatic418967fa.accept_20_3_15_9_1_6456 23 135 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 135 209 (accept_3_2 22 135 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 135 209 (Polychromatic418967fa.accept_10_1_5_9_1_157 21 135 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 135 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 135 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 135 209 (accept_3_2 19 135 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 135 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 135 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 135 209
  (Polychromatic418967fa.accept_7_3_2_6_1_56 17 135 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 135 209 (accept_3_2 16 135 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 135 209 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 135 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 135 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 135 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 209 (accept_3_2 13 135 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 135 209 (Polychromatic418967fa.accept_13_12_5_1_1_1383 12 135 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 135 209
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 135 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 135 209 (accept_3_2 10 135 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  135 209 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 135 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 135 209 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 135 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 209 (accept_3_2 7 135 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 135 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 135 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 135 209
  (Polychromatic418967fa.accept_20_5_15_9_1_9446 5 135 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 135 209 (accept_3_2 4 135 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  135 209 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 135 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 135 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 135 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 209 (accept_3_2 1 135 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 135 209)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 76 134 209 (Eq.refl Bool.true) (allA_succ_of_accept 75 134 209 (Polychromatic418967fa.accept_4_3_2_1_1_50
  75 134 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 134 209
  (Polychromatic418967fa.accept_21_11_8_20_1_4591 74 134 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 134 209 (accept_3_2 73 134 209 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 134 209 (Polychromatic418967fa.accept_7_2_1_6_1_173 72 134 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 134 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 134 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 134 209 (accept_3_2 70 134 209
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 134 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 69
  134 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 134 209
  (Polychromatic418967fa.accept_7_5_1_6_1_163 68 134 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 134 209 (accept_3_2 67 134 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 134 209 (Polychromatic418967fa.accept_9_3_8_2_1_162 66 134 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 134 209 (Polychromatic418967fa.accept_7_2_1_6_1_173 65 134 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 134 209 (accept_3_2 64 134 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 134 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 134 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 134 209
  (Polychromatic418967fa.accept_13_10_4_1_1_2142 62 134 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 134 209 (accept_3_2 61 134 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 134 209 (Polychromatic418967fa.accept_9_6_8_2_1_410 60 134 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 134 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 134 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 134 209 (accept_3_2 58 134 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 134 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 134 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 134 209
  (Polychromatic418967fa.accept_12_8_2_5_1_844 56 134 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 134 209 (accept_3_2 55 134 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 134 209 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 134 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 134 209 (Polychromatic418967fa.accept_10_3_4_9_1_15 53 134 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 134 209 (accept_3_2 52 134 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 134 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 134 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 134 209
  (Polychromatic418967fa.accept_9_5_8_2_1_409 50 134 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 134 209 (accept_3_2 49 134 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 134 209 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 134 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 134 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 134 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 134 209 (accept_3_2 46 134 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 134 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 134 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 134 209
  (Polychromatic418967fa.accept_7_2_1_6_1_173 44 134 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 134 209 (accept_3_2 43 134 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 134 209 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 134 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 134 209 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 134 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 134 209 (accept_3_2 40 134 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 134 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 134 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 134 209
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 38 134 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 134 209 (accept_3_2 37 134 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 134 209 (Polychromatic418967fa.accept_13_10_4_1_1_2142 36 134 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 134 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 134 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 134 209 (accept_3_2 34 134 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 134 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 134 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 134 209
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 134 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 134 209 (accept_3_2 31 134 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 134 209 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 134 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 134 209 (Polychromatic418967fa.accept_13_3_4_1_1_363 29 134 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 134 209 (accept_3_2 28 134 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 134 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 134 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 134 209
  (Polychromatic418967fa.accept_7_5_1_6_1_163 26 134 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 134 209 (accept_3_2 25 134 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 134 209 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 134 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 134 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 134 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 134 209 (accept_3_2 22 134 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 134 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 134 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 134 209
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 134 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 134 209 (accept_3_2 19 134 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 134 209 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 134 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 134 209 (Polychromatic418967fa.accept_21_17_8_20_1_7805 17 134 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 134 209 (accept_3_2 16 134 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 134 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 134 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 134 209
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 134 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 134 209 (accept_3_2 13 134 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 134 209 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 134 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 134 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 134 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 134 209 (accept_3_2 10 134 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 134 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 134 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 134 209
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 134 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 134 209 (accept_3_2 7 134 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  134 209 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 134 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 134 209 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 134 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 134 209 (accept_3_2 4 134 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 134 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 134 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 134 209
  (Polychromatic418967fa.accept_7_2_1_6_1_173 2 134 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 134 209 (accept_3_2 1 134 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134
  209)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 133 209 (Eq.refl
  Bool.true) (allA_of_3_0 77 133 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 78 132 209 (Eq.refl Bool.true)
  (allA_succ_of_gcd 77 132 209 11 7 12 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 76 132 209 (accept_3_2 76 132 209 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 132 209 (Polychromatic418967fa.accept_9_3_6_2_1_160 75 132 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 132 209 (Polychromatic418967fa.accept_13_9_2_1_1_813 74 132
  209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 132 209 (accept_3_2 73 132
  209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 132 209
  (Polychromatic418967fa.accept_16_8_4_1_1_2102 72 132 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 132 209 (Polychromatic418967fa.accept_9_8_6_2_1_744 71 132 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 132 209 (accept_3_2 70 132 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 132 209 (Polychromatic418967fa.accept_8_5_4_1_1_111 69 132 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 132 209 (Polychromatic418967fa.accept_9_5_6_2_1_161
  68 132 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 132 209 (accept_3_2 67
  132 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 132 209 11 6 12 19 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 132 209
  (Polychromatic418967fa.accept_21_2_6_20_1_6059 65 132 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 132 209 (accept_3_2 64 132 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 132 209 (Polychromatic418967fa.accept_14_7_6_13_1_4111 63 132 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 132 209 (Polychromatic418967fa.accept_9_8_6_2_1_744 62 132 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 132 209 (accept_3_2 61 132 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 132 209 (Polychromatic418967fa.accept_16_12_4_1_1_1257 60 132 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 132 209
  (Polychromatic418967fa.accept_9_5_6_2_1_161 59 132 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 132 209 (accept_3_2 58 132 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 132 209 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 132 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 132 209 (Polychromatic418967fa.accept_15_11_12_14_1_2612 56 132 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 132 209 11 5 12 19 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 132 209
  (Polychromatic418967fa.accept_14_12_6_13_1_3173 54 132 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 132 209 (Polychromatic418967fa.accept_8_5_4_1_1_111 53 132 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 132 209 (accept_3_2 52 132 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 132 209 (Polychromatic418967fa.accept_10_1_2_9_1_152 51 132 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 132 209
  (Polychromatic418967fa.accept_9_5_6_2_1_161 50 132 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 132 209 (accept_3_2 49 132 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 132 209 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 132 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 132 209 (Polychromatic418967fa.accept_10_7_2_9_1_775 47 132 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 132 209 (accept_3_2 46 132 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 132 209 (Polychromatic418967fa.accept_8_5_4_1_1_111 45 132 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 132 209 11 4 12 19 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 132 209 (accept_3_2 43
  132 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 132 209
  (Polychromatic418967fa.accept_13_3_2_1_1_2907 42 132 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 132 209 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 132 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 132 209 (accept_3_2 40 132 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 132 209 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 132 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 132 209
  (Polychromatic418967fa.accept_13_12_2_1_1_2909 38 132 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 132 209 (accept_3_2 37 132 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 132 209 (Polychromatic418967fa.accept_21_15_6_20_1_12272 36 132 209 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 35 132 209 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 132 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 132 209 (accept_3_2 34 132 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 132 209 11 3 12 19 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 132 209 (Polychromatic418967fa.accept_9_5_6_2_1_161 32
  132 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 132 209 (accept_3_2 31
  132 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 132 209
  (Polychromatic418967fa.accept_9_3_6_2_1_160 30 132 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 132 209 (Polychromatic418967fa.accept_8_5_4_1_1_111 29 132 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 132 209 (accept_3_2 28 132 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 132 209 (Polychromatic418967fa.accept_10_7_2_9_1_775 27 132 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 132 209
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 132 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 132 209 (accept_3_2 25 132 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 132 209 (Polychromatic418967fa.accept_15_9_12_14_1_963 24 132 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 132 209 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 132 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 132 209 11 2 12 19 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 132 209
  (Polychromatic418967fa.accept_8_5_4_1_1_111 21 132 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 132 209 (Polychromatic418967fa.accept_23_20_17_2_1_12300 20 132 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 132 209 (accept_3_2 19 132 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 132 209 (Polychromatic418967fa.accept_21_18_6_20_1_9242 18 132 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 132 209
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 132 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 132 209 (accept_3_2 16 132 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 132 209 (Polychromatic418967fa.accept_17_15_13_5_1_9877 15 132 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 132 209 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 132 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 132 209 (accept_3_2 13 132 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 132 209 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 132 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 11 132 209 11 1 12 19 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 132 209 (accept_3_2 10 132 209
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 132 209 (Polychromatic418967fa.accept_13_9_2_1_1_813 9
  132 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 132 209
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 132 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 132 209 (accept_3_2 7 132 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  132 209 (Polychromatic418967fa.accept_13_6_2_1_1_2137 6 132 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 132 209 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 132 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 132 209 (accept_3_2 4 132 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 132 209 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 132 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 132 209
  (Polychromatic418967fa.accept_15_2_12_14_1_1709 2 132 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 132 209 (accept_3_2 1 132 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132
  209)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 79 131 209 (Eq.refl
  Bool.true) (allA_succ_of_accept 78 131 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 131 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 131 209
  (Polychromatic418967fa.accept_16_13_3_1_1_2100 77 131 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 131 209 (accept_3_2 76 131 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 131 209 (Polychromatic418967fa.accept_9_3_5_2_1_28 75 131 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 131 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 131 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 131 209 (accept_3_2 73 131 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 131 209 (Polychromatic418967fa.accept_10_2_1_9_1_1248 72 131 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 131 209
  (Polychromatic418967fa.accept_7_1_5_6_1_59 71 131 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 131 209 (accept_3_2 70 131 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 131 209 (Polychromatic418967fa.accept_9_6_5_2_1_421 69 131 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 131 209 (Polychromatic418967fa.accept_10_8_1_9_1_413 68 131 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 131 209 (accept_3_2 67 131 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 131 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 131 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 131 209
  (Polychromatic418967fa.accept_10_5_1_9_1_791 65 131 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 131 209 (accept_3_2 64 131 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 131 209 (Polychromatic418967fa.accept_15_3_11_14_1_1705 63 131 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 131 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 131 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 131 209 (accept_3_2 61 131 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 131 209 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 131 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 131 209
  (Polychromatic418967fa.accept_17_8_12_5_1_1577 59 131 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 131 209 (accept_3_2 58 131 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 131 209 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 131 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 131 209 (Polychromatic418967fa.accept_21_14_5_20_1_12299 56 131 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 131 209 (accept_3_2 55 131 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 131 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 131 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 131 209
  (Polychromatic418967fa.accept_7_4_5_6_1_344 53 131 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 131 209 (accept_3_2 52 131 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 131 209 (Polychromatic418967fa.accept_9_6_5_2_1_421 51 131 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 131 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 131 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 131 209 (accept_3_2 49 131 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 131 209 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 131 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 131 209
  (Polychromatic418967fa.accept_22_3_21_11_1_12298 47 131 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 131 209 (accept_3_2 46 131 209 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 131 209 (Polychromatic418967fa.accept_10_5_1_9_1_791 45 131 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 131 209 (Polychromatic418967fa.accept_9_8_5_2_1_422 44 131 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 131 209 (accept_3_2 43 131 209
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 131 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 42
  131 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 131 209
  (Polychromatic418967fa.accept_17_7_12_5_1_1580 41 131 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 131 209 (accept_3_2 40 131 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 131 209 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 131 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 131 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 131 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 131 209 (accept_3_2 37 131 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 131 209 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 131 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 131 209
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 131 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 131 209 (accept_3_2 34 131 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 131 209 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 131 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 131 209 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 131 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 131 209 (accept_3_2 31 131 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 131 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 131 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 131 209
  (Polychromatic418967fa.accept_7_1_5_6_1_59 29 131 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 131 209 (accept_3_2 28 131 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 131 209 (Polychromatic418967fa.accept_15_12_11_14_1_3464 27 131 209 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 26 131 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 131 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 131 209 (accept_3_2 25 131 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 131 209 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 131 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 131 209
  (Polychromatic418967fa.accept_21_2_5_20_1_7789 23 131 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 131 209 (accept_3_2 22 131 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 131 209 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 131 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 131 209 (Polychromatic418967fa.accept_14_6_5_13_1_367 20 131 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 131 209 (accept_3_2 19 131 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 131 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 131 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 131 209
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 131 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 131 209 (accept_3_2 16 131 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 131 209 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 131 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 131 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 131 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 131 209 (accept_3_2 13 131 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 131 209 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 131 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 131 209
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 131 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 131 209 (accept_3_2 10 131 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  131 209 (Polychromatic418967fa.accept_17_9_12_5_1_219 9 131 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 131 209 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 131 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 131 209 (accept_3_2 7 131 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 131 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 131 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 131 209
  (Polychromatic418967fa.accept_10_5_1_9_1_791 5 131 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 131 209 (accept_3_2 4 131 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  131 209 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 131 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 131 209 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 131 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 131 209 (accept_3_2 1 131 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 131 209)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 80 130 209 (Eq.refl Bool.true) (allA_of_3_0 80 130 209 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 81 129 209 (Eq.refl Bool.true) (allA_succ_of_accept 80 129 209 (Polychromatic418967fa.accept_6_2_3_5_1_26
  80 129 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 129 209 (accept_3_2 79
  129 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 129 209
  (Polychromatic418967fa.accept_9_6_3_2_1_431 78 129 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 129 209 (Polychromatic418967fa.accept_9_5_3_2_1_171 77 129 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 129 209 (accept_3_2 76 129 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 129 209 (Polychromatic418967fa.accept_12_3_9_5_1_853 75 129 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 129 209
  (Polychromatic418967fa.accept_6_2_3_5_1_26 74 129 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 129 209 (accept_3_2 73 129 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 129 209 (Polychromatic418967fa.accept_7_2_3_6_1_4 72 129 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 129 209 (Polychromatic418967fa.accept_9_8_3_2_1_417 71 129 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 129 209 (accept_3_2 70 129 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 129 209 (Polychromatic418967fa.accept_9_6_3_2_1_431 69 129 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 129 209
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 129 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 129 209 (accept_3_2 67 129 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 129 209 (Polychromatic418967fa.accept_14_10_3_13_1_1530 66 129 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 129 209 (Polychromatic418967fa.accept_7_2_3_6_1_4 65 129 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 129 209 (accept_3_2 64 129 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 129 209 (Polychromatic418967fa.accept_12_3_9_5_1_853 63 129 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 129 209
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 129 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 129 209 (accept_3_2 61 129 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 129 209 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 129 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 129 209 (Polychromatic418967fa.accept_9_5_3_2_1_171 59 129 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 129 209 (accept_3_2 58 129 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 129 209 (Polychromatic418967fa.accept_13_5_12_1_1_2123 57 129 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 129 209
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 129 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 129 209 (accept_3_2 55 129 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 129 209 (Polychromatic418967fa.accept_13_2_12_1_1_343 54 129 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 129 209 (Polychromatic418967fa.accept_7_4_3_6_1_340 53 129 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 129 209 (accept_3_2 52 129 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 129 209 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 129 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 129 209
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 129 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 129 209 (accept_3_2 49 129 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 129 209 (Polychromatic418967fa.accept_17_14_10_5_1_8628 48 129 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 129 209 (Polychromatic418967fa.accept_13_8_12_1_1_4662 47 129 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 129 209 (accept_3_2 46 129 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 129 209 (Polychromatic418967fa.accept_22_1_19_11_1_12229 45
  129 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 129 209
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 129 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 129 209 (accept_3_2 43 129 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 129 209 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 129 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 129 209 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 129 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 129 209 (accept_3_2 40 129 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 129 209 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 129 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 129 209
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 129 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 129 209 (accept_3_2 37 129 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 129 209 (Polychromatic418967fa.accept_15_6_9_14_1_3457 36 129 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 129 209 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 129 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 129 209 (accept_3_2 34 129 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 129 209 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 129 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 129 209
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 129 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 129 209 (accept_3_2 31 129 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 129 209 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 129 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 129 209 (Polychromatic418967fa.accept_17_12_10_5_1_4756 29 129 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 129 209 (accept_3_2 28 129 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 129 209 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 129
  209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 129 209
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 129 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 129 209 (accept_3_2 25 129 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 129 209 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 129 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 129 209 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 129 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 209 (accept_3_2 22 129 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 129 209 (Polychromatic418967fa.accept_13_8_12_1_1_4662 21 129 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 129 209
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 129 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 129 209 (accept_3_2 19 129 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 129 209 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 129 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 129 209 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 129 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 209 (accept_3_2 16 129 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 129 209 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 129 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 129 209
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 129 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 129 209 (accept_3_2 13 129 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 129 209 (Polychromatic418967fa.accept_15_12_9_14_1_2635 12 129 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 129 209 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 129 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 209 (accept_3_2 10 129 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 129 209 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 129 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 129 209
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 129 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 129 209 (accept_3_2 7 129 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  129 209 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 129 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 129 209 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 129 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 209 (accept_3_2 4 129 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 129 209 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 129 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 129 209
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 129 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 129 209 (accept_3_2 1 129 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129
  209))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 82 128 209 (Eq.refl
  Bool.true) (allA_succ_of_accept 81 128 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 128 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 128 209 (Polychromatic418967fa.accept_7_3_2_6_1_56 80
  128 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 128 209 (accept_3_2 79
  128 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 128 209
  (Polychromatic418967fa.accept_7_1_2_6_1_55 78 128 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 128 209 (Polychromatic418967fa.accept_10_7_8_9_1_785 77 128 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 128 209 (accept_3_2 76 128 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 128 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 128 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 128 209 (Polychromatic418967fa.accept_7_4_2_6_1_337
  74 128 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 128 209 (accept_3_2 73
  128 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 128 209
  (Polychromatic418967fa.accept_13_7_11_1_1_2903 72 128 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 128 209 (Polychromatic418967fa.accept_7_1_2_6_1_55 71 128 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 128 209 (accept_3_2 70 128 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 128 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 128 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 128 209
  (Polychromatic418967fa.accept_13_3_11_1_1_2122 68 128 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 128 209 (accept_3_2 67 128 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 128 209 (Polychromatic418967fa.accept_7_3_2_6_1_56 66 128 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 128 209 (Polychromatic418967fa.accept_15_5_8_14_1_432 65 128 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 128 209 (accept_3_2 64 128 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 128 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 128 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 128 209
  (Polychromatic418967fa.accept_12_2_8_5_1_408 62 128 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 128 209 (accept_3_2 61 128 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 128 209 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 128 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 128 209 (Polychromatic418967fa.accept_7_3_2_6_1_56 59 128 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 128 209 (accept_3_2 58 128 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 128 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 128 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 128 209
  (Polychromatic418967fa.accept_21_14_2_20_1_12297 56 128 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 128 209 (accept_3_2 55 128 209 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 128 209 (Polychromatic418967fa.accept_10_4_8_9_1_784 54 128 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 128 209 (Polychromatic418967fa.accept_7_4_2_6_1_337 53 128 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 128 209 (accept_3_2 52 128 209
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 128 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 51
  128 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 128 209
  (Polychromatic418967fa.accept_7_1_2_6_1_55 50 128 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 128 209 (accept_3_2 49 128 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 128 209 (Polychromatic418967fa.accept_13_9_11_1_1_1375 48 128 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 128 209 (Polychromatic418967fa.accept_10_7_8_9_1_785 47 128 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 128 209 (accept_3_2 46 128 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 128 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 128 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 128 209
  (Polychromatic418967fa.accept_10_4_8_9_1_784 44 128 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 128 209 (accept_3_2 43 128 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 128 209 (Polychromatic418967fa.accept_13_3_11_1_1_2122 42 128 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 128 209 (Polychromatic418967fa.accept_10_1_8_9_1_787 41 128 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 128 209 (accept_3_2 40 128 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 128 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 128 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 128 209
  (Polychromatic418967fa.accept_7_3_2_6_1_56 38 128 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 128 209 (accept_3_2 37 128 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 128 209 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 128 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 128 209 (Polychromatic418967fa.accept_13_9_11_1_1_1375 35 128 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 128 209 (accept_3_2 34 128 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 128 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 128 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 128 209
  (Polychromatic418967fa.accept_7_4_2_6_1_337 32 128 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 128 209 (accept_3_2 31 128 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 128 209 (Polychromatic418967fa.accept_17_13_9_5_1_6022 30 128 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 128 209 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 128 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 128 209 (accept_3_2 28 128 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 128 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 128 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 128 209
  (Polychromatic418967fa.accept_12_2_8_5_1_408 26 128 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 128 209 (accept_3_2 25 128 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 128 209 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 128 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 128 209 (Polychromatic418967fa.accept_13_10_11_1_1_2152 23 128 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 128 209 (accept_3_2 22 128 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 128 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 128 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 128 209
  (Polychromatic418967fa.accept_13_7_11_1_1_2903 20 128 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 128 209 (accept_3_2 19 128 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 128 209 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 128 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 128 209 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 128 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 128 209 (accept_3_2 16 128 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 128 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 128 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 128 209
  (Polychromatic418967fa.accept_10_4_8_9_1_784 14 128 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 128 209 (accept_3_2 13 128 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 128 209 (Polychromatic418967fa.accept_13_12_11_1_1_2920 12 128 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 128 209 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 128 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 128 209 (accept_3_2 10 128 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 128 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 128 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 128 209
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 128 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 128 209 (accept_3_2 7 128 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  128 209 (Polychromatic418967fa.accept_15_6_8_14_1_4575 6 128 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 128 209 (Polychromatic418967fa.accept_15_5_8_14_1_432 5 128 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 128 209 (accept_3_2 4 128 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 128 209 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 128 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 128 209
  (Polychromatic418967fa.accept_12_2_8_5_1_408 2 128 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 128 209 (accept_3_2 1 128 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128
  209)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 127 209 (Eq.refl
  Bool.true) (allA_of_3_0 83 127 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 84 126 209 (Eq.refl Bool.true)
  (allA_succ_of_accept 83 126 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 126 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 126 209 (accept_3_2 82 126 209 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 126 209 (Polychromatic418967fa.accept_22_15_16_11_1_546 81 126 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 126 209
  (Polychromatic418967fa.accept_13_2_9_1_1_67 80 126 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 126 209 (accept_3_2 79 126 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 126 209 (Polychromatic418967fa.accept_23_9_11_2_1_12296 78 126 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 126 209 (Polychromatic418967fa.accept_16_13_14_1_1_2094 77 126 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 126 209 (accept_3_2 76 126 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 126 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 126 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 126 209
  (Polychromatic418967fa.accept_20_14_6_9_1_9460 74 126 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 126 209 (accept_3_2 73 126 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 126 209 (Polychromatic418967fa.accept_22_6_16_11_1_12282 72 126 209 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 71 126 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 126 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 126 209 (accept_3_2 70 126 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 126 209 (Polychromatic418967fa.accept_15_9_6_14_1_2627 69 126
  209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 126 209
  (Polychromatic418967fa.accept_15_8_6_14_1_975 68 126 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 126 209 (accept_3_2 67 126 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 126 209 (Polychromatic418967fa.accept_17_15_7_5_1_9836 66 126 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 126 209 (Polychromatic418967fa.accept_10_5_6_9_1_2235 65 126 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 126 209 (accept_3_2 64 126 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 126 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 126 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 126 209
  (Polychromatic418967fa.accept_13_10_9_1_1_5609 62 126 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 126 209 (accept_3_2 61 126 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 126 209 (Polychromatic418967fa.accept_13_8_9_1_1_2147 60 126 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 126 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 126 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 126 209 (accept_3_2 58 126 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 126 209 (Polychromatic418967fa.accept_13_5_9_1_1_1405 57 126 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 126 209
  (Polychromatic418967fa.accept_24_8_6_17_1_5282 56 126 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 126 209 (accept_3_2 55 126 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 126 209 (Polychromatic418967fa.accept_13_2_9_1_1_67 54 126 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 126 209 (Polychromatic418967fa.accept_10_3_6_9_1_779 53 126 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 126 209 (accept_3_2 52 126 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 126 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 126 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 126 209
  (Polychromatic418967fa.accept_13_11_9_1_1_1407 50 126 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 126 209 (accept_3_2 49 126 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 126 209 (Polychromatic418967fa.accept_22_4_16_11_1_4197 48 126 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 126 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 126 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 126 209 (accept_3_2 46 126 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 126 209 (Polychromatic418967fa.accept_10_5_6_9_1_2235 45 126 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 126 209
  (Polychromatic418967fa.accept_13_5_9_1_1_1405 44 126 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 126 209 (accept_3_2 43 126 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 126 209 (Polychromatic418967fa.accept_22_20_16_11_1_7421 42 126 209 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 41 126 209 (Polychromatic418967fa.accept_13_2_9_1_1_67 41 126 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 126 209 (accept_3_2 40 126 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 126 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 126 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 126 209
  (Polychromatic418967fa.accept_15_8_6_14_1_975 38 126 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 126 209 (accept_3_2 37 126 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 126 209 (Polychromatic418967fa.accept_13_10_9_1_1_5609 36 126 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 126 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 126 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 126 209 (accept_3_2 34 126 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 126 209 (Polychromatic418967fa.accept_10_3_6_9_1_779 33 126 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 126 209
  (Polychromatic418967fa.accept_13_6_9_1_1_5604 32 126 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 126 209 (accept_3_2 31 126 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 126 209 (Polychromatic418967fa.accept_20_10_6_9_1_4989 30 126 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 126 209 (Polychromatic418967fa.accept_16_13_14_1_1_2094 29 126 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 126 209 (accept_3_2 28 126 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 126 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 126 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 126 209
  (Polychromatic418967fa.accept_17_9_7_5_1_1566 26 126 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 126 209 (accept_3_2 25 126 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 126 209 (Polychromatic418967fa.accept_13_11_9_1_1_1407 24 126 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 126 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 126 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 126 209 (accept_3_2 22 126 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 126 209 (Polychromatic418967fa.accept_13_8_9_1_1_2147 21 126 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 126 209
  (Polychromatic418967fa.accept_15_5_6_14_1_1721 20 126 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 126 209 (accept_3_2 19 126 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 126 209 (Polychromatic418967fa.accept_13_5_9_1_1_1405 18 126 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 126 209 (Polychromatic418967fa.accept_20_17_6_9_1_6434 17 126 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 126 209 (accept_3_2 16 126 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 126 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 126 209
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 126 209
  (Polychromatic418967fa.accept_20_14_6_9_1_9460 14 126 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 126 209 (accept_3_2 13 126 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 126 209 (Polychromatic418967fa.accept_17_12_7_5_1_8659 12 126 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 126 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 126 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 126 209 (accept_3_2 10 126 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 126 209 (Polychromatic418967fa.accept_15_9_6_14_1_2627 9 126 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 126 209
  (Polychromatic418967fa.accept_13_8_9_1_1_2147 8 126 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 126 209 (accept_3_2 7 126 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  126 209 (Polychromatic418967fa.accept_13_6_9_1_1_5604 6 126 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 126 209 (Polychromatic418967fa.accept_10_5_6_9_1_2235 5 126 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 126 209 (accept_3_2 4 126 209 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 126 209 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 126 209 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 126 209
  (Polychromatic418967fa.accept_13_2_9_1_1_67 2 126 209 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 126 209 (accept_3_2 1 126 209 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  209))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_209_segment_000)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


