-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch193
-- name    : Polychromatic418967fa_Branch193
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:20:23.869638+00:00
-- url     : https://prove2.me/theorems/71c1c635-8248-44d4-804c-132b7f3194ba
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch193_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_193 : allB 193 193 :=
  allB_succ' 2 192 193 (Eq.refl Bool.true) (allA_succ_of_accept 1 192 193 (Polychromatic418967fa.accept_7_1_3_4_1_128 1
  192 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 192 193)) (allB_succ' 3 191 193
  (Eq.refl Bool.true) (allA_of_3_1 3 191 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 190 193 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 190 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 190 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 190 193 (accept_3_3 2 190 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 190 193 (Polychromatic418967fa.accept_13_1_8_11_1_724 1 190 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 190 193)))) (allB_succ' 5 189 193 (Eq.refl Bool.true)
  (allA_succ_of_accept 4 189 193 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 189 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 189 193 (Polychromatic418967fa.accept_12_3_9_1_1_290 3 189 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 189 193 (accept_3_3 2 189 193
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 189 193 (Polychromatic418967fa.accept_13_1_7_11_1_702
  1 189 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 189 193))))) (allB_succ' 6 188 193
  (Eq.refl Bool.true) (allA_of_3_1 6 188 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 187 193 (Eq.refl
  Bool.true) (allA_succ_of_accept 6 187 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 187 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 187 193 (accept_3_3 5 187 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 187 193 (Polychromatic418967fa.accept_10_4_7_3_1_54 4 187 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 187 193
  (Polychromatic418967fa.accept_9_3_7_4_1_53 3 187 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 187 193 (accept_3_3 2 187 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  187 193 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 187 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 187 193))))))) (allB_succ' 8 186 193 (Eq.refl Bool.true) (allA_succ_of_accept 7 186 193
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 186 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 186 193 (Polychromatic418967fa.accept_13_6_4_11_1_282 6 186 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 186 193 (accept_3_3 5 186 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 186 193 (Polychromatic418967fa.accept_15_4_6_13_1_956 4 186 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 186 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 3
  186 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 186 193 (accept_3_3 2 186
  193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 186 193 (Polychromatic418967fa.accept_9_1_6_4_1_49
  1 186 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186 193)))))))) (allB_succ' 9 185 193
  (Eq.refl Bool.true) (allA_of_3_1 9 185 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 184 193 (Eq.refl
  Bool.true) (allA_succ_of_accept 9 184 193 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 184 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 184 193 (accept_3_3 8 184 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 184 193 (Polychromatic418967fa.accept_10_7_4_3_1_560 7 184 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 184 193
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 184 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 184 193 (accept_3_3 5 184 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  184 193 (Polychromatic418967fa.accept_13_4_2_11_1_733 4 184 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 184 193 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 184 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 184 193 (accept_3_3 2 184 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 184 193 (Polychromatic418967fa.accept_30_1_4_13_1_11237 1 184 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 184 193)))))))))) (allB_succ' 11 183 193 (Eq.refl
  Bool.true) (allA_succ_of_accept 10 183 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 183 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 183 193 (Polychromatic418967fa.accept_12_9_3_1_1_303 9
  183 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 183 193 (accept_3_3 8 183
  193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 183 193
  (Polychromatic418967fa.accept_9_7_3_4_1_218 7 183 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 183 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 183 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 183 193 (accept_3_3 5 183 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 183 193 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 183 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 183 193 (Polychromatic418967fa.accept_7_3_1_4_1_121 3
  183 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 183 193 (accept_3_3 2 183
  193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 183 193 (Polychromatic418967fa.accept_9_1_3_4_1_47
  1 183 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 183 193))))))))))) (allB_succ' 12 182
  193 (Eq.refl Bool.true) (allA_of_3_1 12 182 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 181 193
  (Eq.refl Bool.true) (allA_succ_of_accept 12 181 193 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 181 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 181 193 (accept_3_3 11 181 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 181 193 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 181 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 181 193
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 181 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 181 193 (accept_3_3 8 181 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  181 193 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 181 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 181 193 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 181 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 181 193 (accept_3_3 5 181 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 181 193 (Polychromatic418967fa.accept_8_4_5_1_1_299 4 181 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 181 193
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 181 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 181 193 (accept_3_3 2 181 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  181 193 (Polychromatic418967fa.accept_11_1_5_6_1_397 1 181 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 181 193))))))))))))) (allB_succ' 14 180 193 (Eq.refl Bool.true) (allA_succ_of_accept 13 180 193
  (Polychromatic418967fa.accept_7_6_5_4_1_297 13 180 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 180 193 (Polychromatic418967fa.accept_16_12_4_1_1_1257 12 180 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 180 193 (accept_3_3 11 180 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 180 193 (Polychromatic418967fa.accept_19_10_9_3_1_7009 10 180 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 180 193
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 180 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 180 193 (accept_3_3 8 180 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  180 193 (Polychromatic418967fa.accept_21_7_12_4_1_6493 7 180 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 180 193 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 180 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 180 193 (accept_3_3 5 180 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 180 193 (Polychromatic418967fa.accept_17_4_10_6_1_4869 4 180 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 180 193
  (Polychromatic418967fa.accept_16_3_4_1_1_2996 3 180 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 180 193 (accept_3_3 2 180 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  180 193 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 180 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 180 193)))))))))))))) (allB_succ' 15 179 193 (Eq.refl Bool.true) (allA_of_3_1 15 179 193
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 178 193 (Eq.refl Bool.true) (allA_succ_of_accept 15 178 193
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 178 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 178 193 (accept_3_3 14 178 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 178 193 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 178 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 178 193 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 178 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 178 193 (accept_3_3 11 178 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 178 193 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 178 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 178 193
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 178 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 178 193 (accept_3_3 8 178 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  178 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 178 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 178 193 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 178 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 178 193 (accept_3_3 5 178 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 178 193 (Polychromatic418967fa.accept_11_4_2_6_1_389 4 178 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 178 193
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 178 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 178 193 (accept_3_3 2 178 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  178 193 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 178 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 178 193)))))))))))))))) (allB_succ' 17 177 193 (Eq.refl Bool.true) (allA_succ_of_accept 16 177
  193 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 177 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 177 193 (Polychromatic418967fa.accept_10_5_7_3_1_561 15 177 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 177 193 (accept_3_3 14 177 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 177 193 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 177 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 177 193 (Polychromatic418967fa.accept_7_5_2_4_1_126
  12 177 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 177 193 (accept_3_3 11
  177 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 177 193
  (Polychromatic418967fa.accept_6_4_3_1_1_57 10 177 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 177 193 (Polychromatic418967fa.accept_13_9_8_11_1_725 9 177 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 177 193 (accept_3_3 8 177 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 177 193 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 177 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 177 193 (Polychromatic418967fa.accept_7_6_2_4_1_291 6
  177 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 177 193 (accept_3_3 5 177
  193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 177 193 (Polychromatic418967fa.accept_6_4_3_1_1_57
  4 177 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 177 193
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 177 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 177 193 (accept_3_3 2 177 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  177 193 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 177 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 177 193))))))))))))))))) (allB_succ' 18 176 193 (Eq.refl Bool.true) (allA_of_3_1 18 176 193
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 175 193 (Eq.refl Bool.true) (allA_succ_of_accept 18 175 193
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 175 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 175 193 (accept_3_3 17 175 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 175 193 (Polychromatic418967fa.accept_11_5_10_6_1_793 16 175 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 175 193 (Polychromatic418967fa.accept_23_15_14_9_1_11236 15 175 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 175 193 (accept_3_3 14 175 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 175 193 (Polychromatic418967fa.accept_19_13_4_3_1_2945 13 175
  193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 175 193
  (Polychromatic418967fa.accept_10_2_5_3_1_1408 12 175 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 175 193 (accept_3_3 11 175 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 175 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 175 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 175 193 (Polychromatic418967fa.accept_27_9_13_4_1_7170 9 175 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 175 193 (accept_3_3 8 175 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 175 193 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 175 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 175 193
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 175 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 175 193 (accept_3_3 5 175 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  175 193 (Polychromatic418967fa.accept_13_4_6_11_1_2017 4 175 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 175 193 (Polychromatic418967fa.accept_14_3_7_11_1_765 3 175 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 175 193 (accept_3_3 2 175 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 175 193 (Polychromatic418967fa.accept_15_1_10_13_1_939 1 175 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 175 193))))))))))))))))))) (allB_succ' 20 174 193
  (Eq.refl Bool.true) (allA_succ_of_accept 19 174 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 174 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 174 193
  (Polychromatic418967fa.accept_15_3_9_13_1_1681 18 174 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 174 193 (accept_3_3 17 174 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 174 193 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 174 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 174 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 174 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 174 193 (accept_3_3 14 174 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 174 193 (Polychromatic418967fa.accept_16_13_14_1_1_2094 13 174 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 174 193
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 174 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 174 193 (accept_3_3 11 174 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 174 193 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 174 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 174 193 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 174 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 174 193 (accept_3_3 8 174 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 174 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 174 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 174 193
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 174 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 174 193 (accept_3_3 5 174 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  174 193 (Polychromatic418967fa.accept_15_4_9_13_1_2582 4 174 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 174 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 174 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 174 193 (accept_3_3 2 174 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 174 193 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 174 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174 193)))))))))))))))))))) (allB_succ' 21 173 193
  (Eq.refl Bool.true) (allA_of_3_1 21 173 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 172 193 (Eq.refl
  Bool.true) (allA_succ_of_accept 21 172 193 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 172 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 172 193 (accept_3_3 20 172 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 172 193 (Polychromatic418967fa.accept_18_1_10_13_1_500 19 172 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 172 193
  (Polychromatic418967fa.accept_13_5_3_11_1_1288 18 172 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 172 193 (accept_3_3 17 172 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 172 193 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 172 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 172 193 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 172 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 172 193 (accept_3_3 14 172 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 172 193 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 172 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 172 193
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 172 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 172 193 (accept_3_3 11 172 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 172 193 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 172 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 172 193 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 172 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 172 193 (accept_3_3 8 172 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 172 193 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 172 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 172 193
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 172 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 172 193 (accept_3_3 5 172 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  172 193 (Polychromatic418967fa.accept_16_4_12_1_1_1204 4 172 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 172 193 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 172 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 172 193 (accept_3_3 2 172 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 172 193 (Polychromatic418967fa.accept_10_1_2_3_1_1910 1 172 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 172 193)))))))))))))))))))))) (allB_succ' 23 171 193
  (Eq.refl Bool.true) (allA_succ_of_accept 22 171 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 171 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 171 193
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 171 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 171 193 (accept_3_3 20 171 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 171 193 (Polychromatic418967fa.accept_15_4_6_13_1_956 19 171 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 171 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 171 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 171 193 (accept_3_3 17 171 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 171 193 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 171 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 171 193
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 171 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 171 193 (accept_3_3 14 171 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 171 193 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 171 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 171 193 (Polychromatic418967fa.accept_10_2_1_3_1_233 12 171 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 171 193 (accept_3_3 11 171 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 171 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 171 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 171 193
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 171 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 171 193 (accept_3_3 8 171 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  171 193 (Polychromatic418967fa.accept_14_7_3_11_1_2199 7 171 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 171 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 171 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 171 193 (accept_3_3 5 171 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 171 193 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 171 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 171 193
  (Polychromatic418967fa.accept_13_3_2_11_1_1999 3 171 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 171 193 (accept_3_3 2 171 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  171 193 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 171 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 171 193))))))))))))))))))))))) (allB_succ' 24 170 193 (Eq.refl Bool.true) (allA_of_3_1 24 170
  193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 169 193 (Eq.refl Bool.true) (allA_succ_of_accept 24 169
  193 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 169 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 169 193 (accept_3_3 23 169 193 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 169 193 (Polychromatic418967fa.accept_18_4_7_13_1_3303 22 169 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 169 193 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 169 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 169 193 (accept_3_3 20 169 193
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 169 193 (Polychromatic418967fa.accept_7_5_1_4_1_122
  19 169 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 169 193
  (Polychromatic418967fa.accept_14_4_1_11_1_5026 18 169 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 169 193 (accept_3_3 17 169 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 169 193 (Polychromatic418967fa.accept_10_6_9_3_1_935 16 169 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 169 193 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 169 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 169 193 (accept_3_3 14 169 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 169 193 (Polychromatic418967fa.accept_11_2_4_6_1_2412 13 169 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 169 193
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 169 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 169 193 (accept_3_3 11 169 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 169 193 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 169 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 169 193 (Polychromatic418967fa.accept_15_9_4_13_1_4482 9 169 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 169 193 (accept_3_3 8 169 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 169 193 (Polychromatic418967fa.accept_17_7_16_6_1_3705 7 169
  193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 169 193
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 169 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 169 193 (accept_3_3 5 169 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  169 193 (Polychromatic418967fa.accept_10_4_9_3_1_1907 4 169 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 169 193 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 169 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 169 193 (accept_3_3 2 169 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 169 193 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 169 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 169 193))))))))))))))))))))))))) (allB_succ' 26 168 193
  (Eq.refl Bool.true) (allA_succ_of_accept 25 168 193 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 168 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 168 193
  (Polychromatic418967fa.accept_15_9_3_13_1_1686 24 168 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 168 193 (accept_3_3 23 168 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 168 193 (Polychromatic418967fa.accept_27_22_6_4_1_7186 22 168 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 168 193 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 168 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 168 193 (accept_3_3 20 168 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 168 193 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 168 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 168 193
  (Polychromatic418967fa.accept_19_18_16_3_1_1803 18 168 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 168 193 (accept_3_3 17 168 193 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 168 193 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 168 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 168 193 (Polychromatic418967fa.accept_10_5_8_3_1_229 15 168
  193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 168 193 (accept_3_3 14 168
  193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 168 193
  (Polychromatic418967fa.accept_19_13_16_3_1_6983 13 168 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 168 193 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 168 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 168 193 (accept_3_3 11 168 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 168 193 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 168 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 168 193
  (Polychromatic418967fa.accept_11_9_3_6_1_797 9 168 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 168 193 (accept_3_3 8 168 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  168 193 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 168 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 168 193 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 168 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 168 193 (accept_3_3 5 168 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 168 193 (Polychromatic418967fa.accept_13_4_12_11_1_5362 4 168 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 168 193
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 168 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 168 193 (accept_3_3 2 168 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  168 193 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 168 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 168 193)))))))))))))))))))))))))) (allB_succ' 27 167 193 (Eq.refl Bool.true) (allA_of_3_1 27 167
  193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 166 193 (Eq.refl Bool.true) (allA_succ_of_accept 27 166
  193 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 166 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 166 193 (accept_3_3 26 166 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 166 193 (Polychromatic418967fa.accept_13_12_10_11_1_1279 25 166 193 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 166 193 (Polychromatic418967fa.accept_17_7_13_6_1_811 24 166 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 166 193 (accept_3_3 23 166 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 166 193 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 166 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 166 193
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 166 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 166 193 (accept_3_3 20 166 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 166 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 166 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 166 193 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 166 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 166 193 (accept_3_3 17 166 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 166 193 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 166 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 166 193
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 166 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 166 193 (accept_3_3 14 166 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 166 193 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 166 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 166 193 (Polychromatic418967fa.accept_13_12_10_11_1_1279 12 166 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 166 193 (accept_3_3 11 166 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 166 193 (Polychromatic418967fa.accept_15_10_1_13_1_2609 10 166
  193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 166 193
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 166 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 166 193 (accept_3_3 8 166 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  166 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 166 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 166 193 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 166 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 166 193 (accept_3_3 5 166 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 166 193 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 166 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 166 193
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 166 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 166 193 (accept_3_3 2 166 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  166 193 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 166 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 166 193)))))))))))))))))))))))))))) (allB_succ' 29 165 193 (Eq.refl Bool.true)
  (allA_succ_of_accept 28 165 193 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 165 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 165 193 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 165
  193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 165 193 (accept_3_3 26 165
  193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 165 193
  (Polychromatic418967fa.accept_9_7_3_4_1_218 25 165 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 165 193 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 165 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 165 193 (accept_3_3 23 165 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 165 193 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 165 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 165 193
  (Polychromatic418967fa.accept_13_8_9_11_1_1265 21 165 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 165 193 (accept_3_3 20 165 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 165 193 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 165 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 165 193 (Polychromatic418967fa.accept_10_8_5_3_1_543 18 165 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 165 193 (accept_3_3 17 165 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 165 193 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 165 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 165 193
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 165 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 165 193 (accept_3_3 14 165 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 165 193 (Polychromatic418967fa.accept_16_13_5_1_1_3017 13 165 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 165 193 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 165 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 165 193 (accept_3_3 11 165 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 165 193 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 165 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 165 193
  (Polychromatic418967fa.accept_16_9_5_1_1_1259 9 165 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 165 193 (accept_3_3 8 165 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  165 193 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 165 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 165 193 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 165 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 165 193 (accept_3_3 5 165 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 165 193 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 165 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 165 193
  (Polychromatic418967fa.accept_12_3_9_1_1_290 3 165 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 165 193 (accept_3_3 2 165 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  165 193 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 165 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 165 193))))))))))))))))))))))))))))) (allB_succ' 30 164 193 (Eq.refl Bool.true) (allA_of_3_1 30
  164 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 163 193 (Eq.refl Bool.true) (allA_succ_of_accept 30
  163 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 163 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 163 193 (accept_3_3 29 163 193 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 163 193 (Polychromatic418967fa.accept_18_10_1_13_1_2192 28 163 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 163 193 (Polychromatic418967fa.accept_7_6_2_4_1_291
  27 163 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 163 193 (accept_3_3 26
  163 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 163 193
  (Polychromatic418967fa.accept_9_7_1_4_1_217 25 163 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 163 193 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 163 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 163 193 (accept_3_3 23 163 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 163 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 163 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 163 193 (Polychromatic418967fa.accept_9_3_1_4_1_216
  21 163 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 163 193 (accept_3_3 20
  163 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 163 193
  (Polychromatic418967fa.accept_7_5_2_4_1_126 19 163 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 163 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 163 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 163 193 (accept_3_3 17 163 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 163 193 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 163 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 163 193 (Polychromatic418967fa.accept_9_6_1_4_1_474
  15 163 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 163 193 (accept_3_3 14
  163 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 163 193
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 163 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 163 193 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 163 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 163 193 (accept_3_3 11 163 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 163 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 163 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 163 193 (Polychromatic418967fa.accept_13_9_7_11_1_1292
  9 163 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 163 193 (accept_3_3 8
  163 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 163 193
  (Polychromatic418967fa.accept_9_7_1_4_1_217 7 163 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 163 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 163 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 163 193 (accept_3_3 5 163 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 163 193 (Polychromatic418967fa.accept_13_4_7_11_1_1981 4 163 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 163 193
  (Polychromatic418967fa.accept_9_3_1_4_1_216 3 163 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 163 193 (accept_3_3 2 163 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  163 193 (Polychromatic418967fa.accept_13_1_7_11_1_702 1 163 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 163 193))))))))))))))))))))))))))))))) (allB_succ' 32 162 193 (Eq.refl Bool.true)
  (allA_succ_of_accept 31 162 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 162 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 162 193 (Polychromatic418967fa.accept_13_4_6_11_1_2017 30 162
  193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 162 193 (accept_3_3 29 162
  193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 162 193
  (Polychromatic418967fa.accept_16_12_2_1_1_1215 28 162 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 162 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 162 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 162 193 (accept_3_3 26 162 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 162 193 (Polychromatic418967fa.accept_10_5_2_3_1_239 25 162 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 162 193
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 162 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 162 193 (accept_3_3 23 162 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 162 193 (Polychromatic418967fa.accept_16_6_2_1_1_4081 22 162 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 162 193 (Polychromatic418967fa.accept_10_1_2_3_1_1910 21 162 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 162 193 (accept_3_3 20 162 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 162 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 162 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 162 193
  (Polychromatic418967fa.accept_13_5_6_11_1_1933 18 162 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 162 193 (accept_3_3 17 162 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 162 193 (Polychromatic418967fa.accept_15_1_12_13_1_944 16 162 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 162 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 162 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 162 193 (accept_3_3 14 162 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 162 193 (Polychromatic418967fa.accept_19_13_10_3_1_11235 13 162 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 162 193
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 162 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 162 193 (accept_3_3 11 162 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 162 193 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 162 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 162 193 (Polychromatic418967fa.accept_16_9_2_1_1_3077 9 162 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 162 193 (accept_3_3 8 162 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 162 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 162 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 162 193
  (Polychromatic418967fa.accept_16_6_2_1_1_4081 6 162 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 162 193 (accept_3_3 5 162 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  162 193 (Polychromatic418967fa.accept_13_4_6_11_1_2017 4 162 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 162 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 162 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 162 193 (accept_3_3 2 162 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 162 193 (Polychromatic418967fa.accept_10_1_2_3_1_1910 1 162 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162 193)))))))))))))))))))))))))))))))) (allB_succ' 33
  161 193 (Eq.refl Bool.true) (allA_of_3_1 33 161 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 160 193
  (Eq.refl Bool.true) (allA_succ_of_accept 33 160 193 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 160 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 160 193 (accept_3_3 32 160 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 160 193 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 160 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 160 193
  (Polychromatic418967fa.accept_7_2_6_4_1_29 30 160 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 160 193 (accept_3_3 29 160 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 160 193 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 160 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 160 193 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 160 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 160 193 (accept_3_3 26 160 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 160 193 (Polychromatic418967fa.accept_13_12_4_11_1_1925 25 160 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 160 193
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 160 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 160 193 (accept_3_3 23 160 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 160 193 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 160 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 160 193 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 160 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 160 193 (accept_3_3 20 160 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 160 193 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 160 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 160 193
  (Polychromatic418967fa.accept_15_3_10_13_1_2605 18 160 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 160 193 (accept_3_3 17 160 193 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 160 193 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 160 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 160 193 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 160 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 160 193 (accept_3_3 14 160 193
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 160 193 (Polychromatic418967fa.accept_17_13_7_6_1_827
  13 160 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 160 193
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 160 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 160 193 (accept_3_3 11 160 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 160 193 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 160 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 160 193 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 160 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 160 193 (accept_3_3 8 160 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 160 193 (Polychromatic418967fa.accept_13_7_4_11_1_1967 7 160 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 160 193
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 160 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 160 193 (accept_3_3 5 160 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  160 193 (Polychromatic418967fa.accept_15_4_10_13_1_2565 4 160 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 160 193 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 160 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 160 193 (accept_3_3 2 160 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 160 193 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 160 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 160 193)))))))))))))))))))))))))))))))))) (allB_succ' 35
  159 193 (Eq.refl Bool.true) (allA_succ_of_accept 34 159 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 159 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 159 193
  (Polychromatic418967fa.accept_12_9_3_1_1_303 33 159 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 159 193 (accept_3_3 32 159 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 159 193 (Polychromatic418967fa.accept_13_5_3_11_1_1288 31 159 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 159 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 159 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 159 193 (accept_3_3 29 159 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 159 193 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 159 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 159 193
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 159 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 159 193 (accept_3_3 26 159 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 159 193 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 159 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 159 193 (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 159 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 159 193 (accept_3_3 23 159 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 159 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 159 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 159 193
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 159 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 159 193 (accept_3_3 20 159 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 159 193 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 159 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 159 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 159 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 159 193 (accept_3_3 17 159 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 159 193 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 159 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 159 193
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 159 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 159 193 (accept_3_3 14 159 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 159 193 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 159 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 159 193 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 159 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 159 193 (accept_3_3 11 159 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 159 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 159 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 159 193
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 159 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 159 193 (accept_3_3 8 159 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  159 193 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 159 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 159 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 159 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 159 193 (accept_3_3 5 159 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 159 193 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 159 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 159 193
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 159 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 159 193 (accept_3_3 2 159 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  159 193 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 159 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 159 193))))))))))))))))))))))))))))))))))) (allB_succ' 36 158 193 (Eq.refl Bool.true)
  (allA_of_3_1 36 158 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 157 193 (Eq.refl Bool.true)
  (allA_succ_of_accept 36 157 193 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 157 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 157 193 (accept_3_3 35 157 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 157 193 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 157 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 157 193 (Polychromatic418967fa.accept_13_7_1_11_1_732
  33 157 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 157 193 (accept_3_3 32
  157 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 157 193
  (Polychromatic418967fa.accept_11_9_3_6_1_797 31 157 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 157 193 (Polychromatic418967fa.accept_11_8_3_6_1_1855 30 157 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 157 193 (accept_3_3 29 157 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 157 193 (Polychromatic418967fa.accept_8_4_5_1_1_299 28 157 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 157 193 (Polychromatic418967fa.accept_7_6_3_4_1_294
  27 157 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 157 193 (accept_3_3 26
  157 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 157 193
  (Polychromatic418967fa.accept_10_5_7_3_1_561 25 157 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 157 193 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 157 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 157 193 (accept_3_3 23 157 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 157 193 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 157 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 157 193
  (Polychromatic418967fa.accept_13_8_1_11_1_1284 21 157 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 157 193 (accept_3_3 20 157 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 157 193 (Polychromatic418967fa.accept_11_8_3_6_1_1855 19 157 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 157 193 (Polychromatic418967fa.accept_27_18_22_4_1_9203 18 157 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 157 193 (accept_3_3 17 157 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 157 193 (Polychromatic418967fa.accept_10_6_7_3_1_547 16 157
  193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 157 193
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 157 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 157 193 (accept_3_3 14 157 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 157 193 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 157 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 157 193 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 157 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 157 193 (accept_3_3 11 157 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 157 193 (Polychromatic418967fa.accept_13_10_1_11_1_1961 10 157 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 157 193
  (Polychromatic418967fa.accept_11_9_3_6_1_797 9 157 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 157 193 (accept_3_3 8 157 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  157 193 (Polychromatic418967fa.accept_13_7_1_11_1_732 7 157 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 157 193 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 157 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 157 193 (accept_3_3 5 157 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 157 193 (Polychromatic418967fa.accept_8_4_5_1_1_299 4 157 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 157 193
  (Polychromatic418967fa.accept_13_3_1_11_1_1268 3 157 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 157 193 (accept_3_3 2 157 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  157 193 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 157 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 157 193))))))))))))))))))))))))))))))))))))) (allB_succ' 38 156 193 (Eq.refl Bool.true)
  (allA_succ_of_accept 37 156 193 (Polychromatic418967fa.accept_8_5_4_1_1_111 37 156 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 156 193 (Polychromatic418967fa.accept_16_4_12_1_1_1204 36 156
  193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 156 193 (accept_3_3 35 156
  193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 156 193
  (Polychromatic418967fa.accept_7_6_2_4_1_291 34 156 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 156 193 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 156 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 156 193 (accept_3_3 32 156 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 156 193 (Polychromatic418967fa.accept_17_14_3_6_1_3716 31 156 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 156 193
  (Polychromatic418967fa.accept_19_11_4_3_1_5534 30 156 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 156 193 (accept_3_3 29 156 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 156 193 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 156 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 156 193 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 156 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 156 193 (accept_3_3 26 156 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 156 193 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 156 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 156 193
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 156 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 156 193 (accept_3_3 23 156 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 156 193 (Polychromatic418967fa.accept_15_7_6_13_1_936 22 156 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 156 193 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 156 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 156 193 (accept_3_3 20 156 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 156 193 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 156 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 156 193
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 156 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 156 193 (accept_3_3 17 156 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 156 193 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 156 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 156 193 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 156 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 156 193 (accept_3_3 14 156 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 156 193 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 156 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 156 193
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 156 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 156 193 (accept_3_3 11 156 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 156 193 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 156 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 156 193 (Polychromatic418967fa.accept_10_9_6_3_1_545 9 156 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 156 193 (accept_3_3 8 156 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 156 193 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 156 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 156 193
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 156 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 156 193 (accept_3_3 5 156 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  156 193 (Polychromatic418967fa.accept_11_4_2_6_1_389 4 156 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 156 193 (Polychromatic418967fa.accept_18_3_12_13_1_3307 3 156 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 156 193 (accept_3_3 2 156 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 156 193 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 156 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156 193))))))))))))))))))))))))))))))))))))))
  (allB_succ' 39 155 193 (Eq.refl Bool.true) (allA_of_3_1 39 155 193 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 40 154 193 (Eq.refl Bool.true) (allA_succ_of_accept 39 154 193 (Polychromatic418967fa.accept_4_3_2_1_1_50
  39 154 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 154 193 (accept_3_3 38
  154 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 154 193
  (Polychromatic418967fa.accept_10_7_4_3_1_560 37 154 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 154 193 (Polychromatic418967fa.accept_15_6_4_13_1_403 36 154 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 154 193 (accept_3_3 35 154 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 154 193 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 154 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 154 193 (Polychromatic418967fa.accept_6_3_4_1_1_8 33
  154 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 154 193 (accept_3_3 32
  154 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 154 193
  (Polychromatic418967fa.accept_4_3_2_1_1_50 31 154 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 154 193 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 154 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 154 193 (accept_3_3 29 154 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 154 193 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 154 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 154 193
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 154 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 154 193 (accept_3_3 26 154 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 154 193 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 154 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 154 193 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 154 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 154 193 (accept_3_3 23 154 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 154 193 (Polychromatic418967fa.accept_17_5_1_6_1_2615 22 154 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 154 193
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 154 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 154 193 (accept_3_3 20 154 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 154 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 154 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 154 193 (Polychromatic418967fa.accept_19_18_2_3_1_4177 18 154 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 154 193 (accept_3_3 17 154 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 154 193 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 154 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 154 193
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 154 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 154 193 (accept_3_3 14 154 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 154 193 (Polychromatic418967fa.accept_21_13_7_4_1_4991 13 154 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 154 193 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 154 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 154 193 (accept_3_3 11 154 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 154 193 (Polychromatic418967fa.accept_15_10_4_13_1_4506 10 154 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 154 193
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 154 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 154 193 (accept_3_3 8 154 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  154 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 154 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 154 193 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 154 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 154 193 (accept_3_3 5 154 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 154 193 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 154 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 154 193
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 154 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 154 193 (accept_3_3 2 154 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  154 193 (Polychromatic418967fa.accept_18_1_10_13_1_500 1 154 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 154 193)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 153 193 (Eq.refl Bool.true)
  (allA_succ_of_accept 40 153 193 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 153 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 153 193 (Polychromatic418967fa.accept_12_3_9_1_1_290 39 153
  193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 153 193 (accept_3_3 38 153
  193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 153 193
  (Polychromatic418967fa.accept_7_2_6_4_1_29 37 153 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 153 193 (Polychromatic418967fa.accept_19_17_1_3_1_4160 36 153 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 153 193 (accept_3_3 35 153 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 153 193 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 153 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 153 193 (Polychromatic418967fa.accept_7_5_6_4_1_117
  33 153 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 153 193 (accept_3_3 32
  153 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 153 193
  (Polychromatic418967fa.accept_7_3_6_4_1_30 31 153 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 153 193 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 153 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 153 193 (accept_3_3 29 153 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 153 193 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 153 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 153 193 (Polychromatic418967fa.accept_11_5_10_6_1_793
  27 153 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 153 193 (accept_3_3 26
  153 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 153 193
  (Polychromatic418967fa.accept_13_12_10_11_1_1279 25 153 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 153 193 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 153 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 153 193 (accept_3_3 23 153 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 153 193 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 153 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 153 193
  (Polychromatic418967fa.accept_13_8_10_11_1_2730 21 153 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 153 193 (accept_3_3 20 153 193 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 153 193 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 153 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 153 193 (Polychromatic418967fa.accept_16_2_9_1_1_6404 18 153
  193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 153 193 (accept_3_3 17 153
  193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 153 193
  (Polychromatic418967fa.accept_6_4_3_1_1_57 16 153 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 153 193 (Polychromatic418967fa.accept_12_3_9_1_1_290 15 153 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 153 193 (accept_3_3 14 153 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 153 193 (Polychromatic418967fa.accept_16_13_9_1_1_3022 13 153 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 153 193
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 153 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 153 193 (accept_3_3 11 153 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 153 193 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 153 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 153 193 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 153 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 153 193 (accept_3_3 8 153 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 193 (Polychromatic418967fa.accept_21_7_6_4_1_3445 7 153 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 153 193
  (Polychromatic418967fa.accept_18_6_9_13_1_3320 6 153 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 153 193 (accept_3_3 5 153 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  153 193 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 153 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 153 193 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 153 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 153 193 (accept_3_3 2 153 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 193 (Polychromatic418967fa.accept_13_1_10_11_1_1280 1 153 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 153 193)))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 42 152 193 (Eq.refl Bool.true) (allA_of_3_1 42 152 193 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 43 151 193 (Eq.refl Bool.true) (allA_succ_of_accept 42 151 193 (Polychromatic418967fa.accept_4_2_3_1_1_2
  42 151 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 151 193 (accept_3_3 41
  151 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 151 193
  (Polychromatic418967fa.accept_13_1_8_11_1_724 40 151 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 151 193 (Polychromatic418967fa.accept_9_3_7_4_1_53 39 151 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 151 193 (accept_3_3 38 151 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 151 193 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 151 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 151 193 (Polychromatic418967fa.accept_11_3_8_6_1_788
  36 151 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 151 193 (accept_3_3 35
  151 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 151 193
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 151 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 151 193 (Polychromatic418967fa.accept_9_6_7_4_1_212 33 151 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 151 193 (accept_3_3 32 151 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 151 193 (Polychromatic418967fa.accept_17_14_15_6_1_4819 31 151 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 151 193
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 151 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 151 193 (accept_3_3 29 151 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 151 193 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 151 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 151 193 (Polychromatic418967fa.accept_13_1_8_11_1_724 27 151 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 151 193 (accept_3_3 26 151 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 151 193 (Polychromatic418967fa.accept_11_3_8_6_1_788 25 151
  193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 151 193
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 151 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 151 193 (accept_3_3 23 151 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 151 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 151 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 151 193 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 151 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 151 193 (accept_3_3 20 151 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 151 193 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 151 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 151 193
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 151 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 151 193 (accept_3_3 17 151 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 151 193 (Polychromatic418967fa.accept_13_3_8_11_1_1906 16 151 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 151 193 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 151 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 151 193 (accept_3_3 14 151 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 151 193 (Polychromatic418967fa.accept_22_13_19_17_1_9654 13 151 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 151 193
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 151 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 151 193 (accept_3_3 11 151 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 151 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 151 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 151 193 (Polychromatic418967fa.accept_13_9_8_11_1_725 9 151 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 151 193 (accept_3_3 8 151 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 151 193 (Polychromatic418967fa.accept_22_7_19_17_1_9584 7 151 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 151 193
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 151 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 151 193 (accept_3_3 5 151 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  151 193 (Polychromatic418967fa.accept_13_4_8_11_1_1937 4 151 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 151 193 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 151 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 151 193 (accept_3_3 2 151 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 151 193 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 151 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 151 193)))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 44 150 193 (Eq.refl Bool.true) (allA_succ_of_accept 43 150 193 (Polychromatic418967fa.accept_4_3_2_1_1_50
  43 150 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 150 193
  (Polychromatic418967fa.accept_13_3_7_11_1_1904 42 150 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 150 193 (accept_3_3 41 150 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 150 193 (Polychromatic418967fa.accept_13_1_7_11_1_702 40 150 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 150 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 150 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 150 193 (accept_3_3 38 150 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 150 193 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 150 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 150 193
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 150 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 150 193 (accept_3_3 35 150 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 150 193 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 150 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 150 193 (Polychromatic418967fa.accept_19_14_17_3_1_4137 33 150 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 150 193 (accept_3_3 32 150 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 150 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 150 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 150 193
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 150 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 150 193 (accept_3_3 29 150 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 150 193 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 150 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 150 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 150 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 150 193 (accept_3_3 26 150 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 150 193 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 150 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 150 193
  (Polychromatic418967fa.accept_17_7_14_6_1_4882 24 150 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 150 193 (accept_3_3 23 150 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 150 193 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 150 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 150 193 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 150 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 150 193 (accept_3_3 20 150 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 150 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 150 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 150 193
  (Polychromatic418967fa.accept_13_5_7_11_1_3470 18 150 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 150 193 (accept_3_3 17 150 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 150 193 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 150 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 150 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 150 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 150 193 (accept_3_3 14 150 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 150 193 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 150 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 150 193
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 150 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 150 193 (accept_3_3 11 150 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 150 193 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 150 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 150 193 (Polychromatic418967fa.accept_13_9_7_11_1_1292 9 150 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 150 193 (accept_3_3 8 150 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 150 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 150 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 150 193
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 150 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 150 193 (accept_3_3 5 150 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  150 193 (Polychromatic418967fa.accept_13_4_7_11_1_1981 4 150 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 150 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 150 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 150 193 (accept_3_3 2 150 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 150 193 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 150 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150 193))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 45 149 193 (Eq.refl Bool.true) (allA_of_3_1 45 149 193 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 46 148 193 (Eq.refl Bool.true) (allA_succ_of_accept 45 148 193 (Polychromatic418967fa.accept_6_3_4_1_1_8
  45 148 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 148 193 (accept_3_3 44
  148 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 148 193
  (Polychromatic418967fa.accept_11_10_5_6_1_1842 43 148 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 148 193 (Polychromatic418967fa.accept_13_3_5_11_1_716 42 148 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 148 193 (accept_3_3 41 148 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 148 193 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 148 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 148 193 (Polychromatic418967fa.accept_6_3_4_1_1_8 39
  148 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 148 193 (accept_3_3 38
  148 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 148 193
  (Polychromatic418967fa.accept_8_5_4_1_1_111 37 148 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 148 193 (Polychromatic418967fa.accept_10_6_8_3_1_930 36 148 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 148 193 (accept_3_3 35 148 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 148 193 (Polychromatic418967fa.accept_11_1_5_6_1_397 34 148 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 148 193
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 148 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 148 193 (accept_3_3 32 148 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 148 193 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 148 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 148 193 (Polychromatic418967fa.accept_16_14_4_1_1_3049 30 148 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 148 193 (accept_3_3 29 148 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 148 193 (Polychromatic418967fa.accept_16_12_4_1_1_1257 28 148
  193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 148 193
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 148 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 148 193 (accept_3_3 26 148 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 148 193 (Polychromatic418967fa.accept_10_5_8_3_1_229 25 148 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 148 193 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 148 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 148 193 (accept_3_3 23 148 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 148 193 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 148 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 148 193
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 148 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 148 193 (accept_3_3 20 148 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 148 193 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 148 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 148 193 (Polychromatic418967fa.accept_14_4_8_11_1_794 18 148 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 148 193 (accept_3_3 17 148 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 148 193 (Polychromatic418967fa.accept_10_6_8_3_1_930 16 148
  193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 148 193
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 148 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 148 193 (accept_3_3 14 148 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 148 193 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 148 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 148 193 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 148 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 148 193 (accept_3_3 11 148 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 148 193 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 148 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 148 193
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 148 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 148 193 (accept_3_3 8 148 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  148 193 (Polychromatic418967fa.accept_13_7_5_11_1_1927 7 148 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 148 193 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 148 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 148 193 (accept_3_3 5 148 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 148 193 (Polychromatic418967fa.accept_14_4_8_11_1_794 4 148 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 148 193
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 148 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 148 193 (accept_3_3 2 148 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  148 193 (Polychromatic418967fa.accept_10_1_8_3_1_947 1 148 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 148 193)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 147 193 (Eq.refl Bool.true)
  (allA_succ_of_accept 46 147 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 147 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 147 193 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 147
  193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 147 193 (accept_3_3 44 147
  193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 147 193
  (Polychromatic418967fa.accept_9_7_3_4_1_218 43 147 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 147 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 147 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 147 193 (accept_3_3 41 147 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 147 193 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 147 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 147 193
  (Polychromatic418967fa.accept_17_5_11_6_1_4815 39 147 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 147 193 (accept_3_3 38 147 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 147 193 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 147 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 147 193 (Polychromatic418967fa.accept_10_6_7_3_1_547 36 147 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 147 193 (accept_3_3 35 147 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 147 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 147 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 147 193
  (Polychromatic418967fa.accept_9_6_3_4_1_477 33 147 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 147 193 (accept_3_3 32 147 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 147 193 (Polychromatic418967fa.accept_14_3_7_11_1_765 31 147 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 147 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 147 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 147 193 (accept_3_3 29 147 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 147 193 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 147 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 147 193
  (Polychromatic418967fa.accept_18_9_3_13_1_5905 27 147 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 147 193 (accept_3_3 26 147 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 147 193 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 147 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 147 193 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 147 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 147 193 (accept_3_3 23 147 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 147 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 147 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 147 193
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 147 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 147 193 (accept_3_3 20 147 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 147 193 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 147 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 147 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 147 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 147 193 (accept_3_3 17 147 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 147 193 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 147 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 147 193
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 147 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 147 193 (accept_3_3 14 147 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 147 193 (Polychromatic418967fa.accept_11_2_4_6_1_2412 13 147 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 147 193 (Polychromatic418967fa.accept_13_12_4_11_1_1925 12 147 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 147 193 (accept_3_3 11 147 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 147 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 147 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 147 193
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 147 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 147 193 (accept_3_3 8 147 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  147 193 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 147 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 147 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 147 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 147 193 (accept_3_3 5 147 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 147 193 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 147 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 147 193
  (Polychromatic418967fa.accept_14_3_7_11_1_765 3 147 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 147 193 (accept_3_3 2 147 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  147 193 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 147 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 147 193))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 146 193 (Eq.refl
  Bool.true) (allA_of_3_1 48 146 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 145 193 (Eq.refl Bool.true)
  (allA_succ_of_accept 48 145 193 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 145 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 145 193 (accept_3_3 47 145 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 145 193 (Polychromatic418967fa.accept_15_1_10_13_1_939 46 145 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 145 193
  (Polychromatic418967fa.accept_19_7_12_3_1_4169 45 145 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 145 193 (accept_3_3 44 145 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 145 193 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 145 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 145 193 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 145 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 145 193 (accept_3_3 41 145 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 145 193 (Polychromatic418967fa.accept_19_2_12_3_1_5446 40 145 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 145 193
  (Polychromatic418967fa.accept_9_3_1_4_1_216 39 145 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 145 193 (accept_3_3 38 145 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 145 193 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 145 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 145 193 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 145 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 145 193 (accept_3_3 35 145 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 145 193 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 145 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 145 193
  (Polychromatic418967fa.accept_9_6_1_4_1_474 33 145 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 145 193 (accept_3_3 32 145 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 145 193 (Polychromatic418967fa.accept_15_1_10_13_1_939 31 145 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 145 193 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 145 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 145 193 (accept_3_3 29 145 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 145 193 (Polychromatic418967fa.accept_10_8_5_3_1_543 28 145 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 145 193
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 145 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 145 193 (accept_3_3 26 145 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 145 193 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 145 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 145 193 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 145 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 145 193 (accept_3_3 23 145 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 145 193 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 145 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 145 193
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 145 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 145 193 (accept_3_3 20 145 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 145 193 (Polychromatic418967fa.accept_15_4_10_13_1_2565 19 145 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 145 193 (Polychromatic418967fa.accept_10_8_5_3_1_543 18 145 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 145 193 (accept_3_3 17 145 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 145 193 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 145 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 145 193
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 145 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 145 193 (accept_3_3 14 145 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 145 193 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 145 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 145 193 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 145 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 145 193 (accept_3_3 11 145 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 145 193 (Polychromatic418967fa.accept_13_10_2_11_1_1920 10 145 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 145 193
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 145 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 145 193 (accept_3_3 8 145 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  145 193 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 145 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 145 193 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 145 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 145 193 (accept_3_3 5 145 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 145 193 (Polychromatic418967fa.accept_11_4_2_6_1_389 4 145 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 145 193
  (Polychromatic418967fa.accept_9_3_1_4_1_216 3 145 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 145 193 (accept_3_3 2 145 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  145 193 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 145 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 145 193))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 144 193 (Eq.refl
  Bool.true) (allA_succ_of_accept 49 144 193 (Polychromatic418967fa.accept_10_9_4_3_1_539 49 144 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 144 193 (Polychromatic418967fa.accept_13_9_1_11_1_275
  48 144 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 144 193 (accept_3_3 47
  144 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 144 193
  (Polychromatic418967fa.accept_13_7_1_11_1_732 46 144 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 144 193 (Polychromatic418967fa.accept_21_3_18_4_1_11234 45 144 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 144 193 (accept_3_3 44 144 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 144 193 (Polychromatic418967fa.accept_14_1_4_11_1_3036 43 144 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 144 193
  (Polychromatic418967fa.accept_13_3_1_11_1_1268 42 144 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 144 193 (accept_3_3 41 144 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 144 193 (Polychromatic418967fa.accept_11_7_1_6_1_1281 40 144 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 144 193 (Polychromatic418967fa.accept_10_9_4_3_1_539 39 144 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 144 193 (accept_3_3 38 144 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 144 193 (Polychromatic418967fa.accept_10_7_4_3_1_560 37 144
  193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 144 193
  (Polychromatic418967fa.accept_13_10_1_11_1_1961 36 144 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 144 193 (accept_3_3 35 144 193 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 144 193 (Polychromatic418967fa.accept_13_8_1_11_1_1284 34 144 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 144 193 (Polychromatic418967fa.accept_13_7_1_11_1_732 33 144
  193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 144 193 (accept_3_3 32 144
  193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 144 193
  (Polychromatic418967fa.accept_17_14_8_6_1_2643 31 144 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 144 193 (Polychromatic418967fa.accept_21_9_18_4_1_4953 30 144 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 144 193 (accept_3_3 29 144 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 144 193 (Polychromatic418967fa.accept_19_9_11_3_1_5580 28 144 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 144 193
  (Polychromatic418967fa.accept_10_7_4_3_1_560 27 144 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 144 193 (accept_3_3 26 144 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 144 193 (Polychromatic418967fa.accept_13_12_1_11_1_1917 25 144 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 144 193 (Polychromatic418967fa.accept_21_3_18_4_1_11234 24 144 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 144 193 (accept_3_3 23 144 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 144 193 (Polychromatic418967fa.accept_13_9_1_11_1_275 22 144
  193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 144 193
  (Polychromatic418967fa.accept_13_8_1_11_1_1284 21 144 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 144 193 (accept_3_3 20 144 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 144 193 (Polychromatic418967fa.accept_10_9_4_3_1_539 19 144 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 144 193 (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 144 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 144 193 (accept_3_3 17 144 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 144 193 (Polychromatic418967fa.accept_11_5_1_6_1_774 16 144
  193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 144 193
  (Polychromatic418967fa.accept_14_1_4_11_1_3036 15 144 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 144 193 (accept_3_3 14 144 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 144 193 (Polychromatic418967fa.accept_19_13_11_3_1_5465 13 144 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 144 193 (Polychromatic418967fa.accept_13_12_1_11_1_1917 12 144 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 144 193 (accept_3_3 11 144 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 144 193 (Polychromatic418967fa.accept_13_10_1_11_1_1961 10 144
  193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 144 193
  (Polychromatic418967fa.accept_10_9_4_3_1_539 9 144 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 144 193 (accept_3_3 8 144 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  144 193 (Polychromatic418967fa.accept_10_7_4_3_1_560 7 144 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 144 193 (Polychromatic418967fa.accept_21_6_18_4_1_4952 6 144 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 144 193 (accept_3_3 5 144 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 144 193 (Polychromatic418967fa.accept_15_4_9_13_1_2582 4 144
  193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 144 193
  (Polychromatic418967fa.accept_13_3_1_11_1_1268 3 144 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 144 193 (accept_3_3 2 144 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  144 193 (Polychromatic418967fa.accept_14_1_4_11_1_3036 1 144 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 144 193)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 143 193 (Eq.refl
  Bool.true) (allA_of_3_1 51 143 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 52 142 193 (Eq.refl Bool.true)
  (allA_succ_of_accept 51 142 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 142 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 142 193 (accept_3_3 50 142 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 142 193 (Polychromatic418967fa.accept_11_5_10_6_1_793 49 142 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 142 193
  (Polychromatic418967fa.accept_7_6_2_4_1_291 48 142 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 142 193 (accept_3_3 47 142 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 142 193 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 142 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 142 193 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 142 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 142 193 (accept_3_3 44 142 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 142 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 142 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 142 193
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 142 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 142 193 (accept_3_3 41 142 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 142 193 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 142 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 142 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 142 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 142 193 (accept_3_3 38 142 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 142 193 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 142 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 142 193
  (Polychromatic418967fa.accept_13_10_12_11_1_731 36 142 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 142 193 (accept_3_3 35 142 193 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 142 193 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 142 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 142 193 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 142 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 142 193 (accept_3_3 32 142 193
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 142 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 31
  142 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 142 193
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 142 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 142 193 (accept_3_3 29 142 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 142 193 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 142 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 142 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 142 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 142 193 (accept_3_3 26 142 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 142 193 (Polychromatic418967fa.accept_10_5_2_3_1_239 25 142 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 142 193
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 142 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 142 193 (accept_3_3 23 142 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 142 193 (Polychromatic418967fa.accept_25_22_17_18_1_11233 22 142 193 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 142 193 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 142 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 142 193 (accept_3_3 20 142 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 142 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 142 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 142 193
  (Polychromatic418967fa.accept_19_18_9_3_1_8430 18 142 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 142 193 (accept_3_3 17 142 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 142 193 (Polychromatic418967fa.accept_11_5_10_6_1_793 16 142 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 142 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 142 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 142 193 (accept_3_3 14 142 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 142 193 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 142 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 142 193
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 142 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 142 193 (accept_3_3 11 142 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 142 193 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 142 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 142 193 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 142 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 142 193 (accept_3_3 8 142 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 142 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 142 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 142 193
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 142 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 142 193 (accept_3_3 5 142 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  142 193 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 142 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 142 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 142 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 142 193 (accept_3_3 2 142 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 142 193 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 142 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142
  193)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 141 193 (Eq.refl Bool.true)
  (allA_succ_of_accept 52 141 193 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 141 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 141 193 (Polychromatic418967fa.accept_12_3_9_1_1_290 51 141
  193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 141 193 (accept_3_3 50 141
  193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 141 193
  (Polychromatic418967fa.accept_15_4_6_13_1_956 49 141 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 141 193 (Polychromatic418967fa.accept_9_3_6_4_1_210 48 141 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 141 193 (accept_3_3 47 141 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 141 193 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 141 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 141 193 (Polychromatic418967fa.accept_7_3_1_4_1_121
  45 141 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 141 193 (accept_3_3 44
  141 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 141 193
  (Polychromatic418967fa.accept_9_7_6_4_1_483 43 141 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 141 193 (Polychromatic418967fa.accept_10_2_1_3_1_233 42 141 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 141 193 (accept_3_3 41 141 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 141 193 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 141 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 141 193 (Polychromatic418967fa.accept_9_3_6_4_1_210
  39 141 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 141 193 (accept_3_3 38
  141 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 141 193
  (Polychromatic418967fa.accept_9_1_6_4_1_49 37 141 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 141 193 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 141 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 141 193 (accept_3_3 35 141 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 141 193 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 141 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 141 193 (Polychromatic418967fa.accept_7_5_1_4_1_122
  33 141 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 141 193 (accept_3_3 32
  141 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 141 193
  (Polychromatic418967fa.accept_7_3_1_4_1_121 31 141 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 141 193 (Polychromatic418967fa.accept_9_3_6_4_1_210 30 141 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 141 193 (accept_3_3 29 141 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 141 193 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 141 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 141 193 (Polychromatic418967fa.accept_12_3_9_1_1_290
  27 141 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 141 193 (accept_3_3 26
  141 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 193
  (Polychromatic418967fa.accept_9_7_6_4_1_483 25 141 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 141 193 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 141 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 141 193 (accept_3_3 23 141 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 141 193 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 141 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 141 193 (Polychromatic418967fa.accept_9_3_6_4_1_210
  21 141 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 141 193 (accept_3_3 20
  141 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 141 193
  (Polychromatic418967fa.accept_7_5_1_4_1_122 19 141 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 141 193 (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 141 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 141 193 (accept_3_3 17 141 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 141 193 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 141 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 141 193 (Polychromatic418967fa.accept_12_3_9_1_1_290
  15 141 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 141 193 (accept_3_3 14
  141 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 193
  (Polychromatic418967fa.accept_19_13_8_3_1_2906 13 141 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 141 193 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 141 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 141 193 (accept_3_3 11 141 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 141 193 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 141 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 141 193 (Polychromatic418967fa.accept_16_9_13_1_1_3069
  9 141 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 141 193 (accept_3_3 8
  141 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 193
  (Polychromatic418967fa.accept_9_7_6_4_1_483 7 141 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 141 193 (Polychromatic418967fa.accept_19_6_8_3_1_11219 6 141 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 141 193 (accept_3_3 5 141 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 141 193 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 141 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 141 193 (Polychromatic418967fa.accept_7_3_1_4_1_121 3
  141 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 141 193 (accept_3_3 2 141
  193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 193 (Polychromatic418967fa.accept_9_1_6_4_1_49
  1 141 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 141
  193))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 140 193 (Eq.refl Bool.true) (allA_of_3_1 54
  140 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 55 139 193 (Eq.refl Bool.true) (allA_succ_of_accept 54
  139 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 139 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 139 193 (accept_3_3 53 139 193 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 139 193 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 139 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 139 193 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 139 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 139 193 (accept_3_3 50 139 193
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 139 193
  (Polychromatic418967fa.accept_20_9_19_13_1_8338 49 139 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 139 193 (Polychromatic418967fa.accept_17_14_3_6_1_3716 48 139 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 139 193 (accept_3_3 47 139 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 139 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 139 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 139 193
  (Polychromatic418967fa.accept_7_3_6_4_1_30 45 139 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 139 193 (accept_3_3 44 139 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 139 193 (Polychromatic418967fa.accept_17_9_3_6_1_11232 43 139 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 139 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 139 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 139 193 (accept_3_3 41 139 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 139 193 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 139 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 139 193
  (Polychromatic418967fa.accept_15_9_4_13_1_4482 39 139 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 139 193 (accept_3_3 38 139 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 139 193 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 139 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 139 193 (Polychromatic418967fa.accept_10_6_9_3_1_935 36 139 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 139 193 (accept_3_3 35 139 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 139 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 139 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 139 193
  (Polychromatic418967fa.accept_7_5_6_4_1_117 33 139 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 139 193 (accept_3_3 32 139 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 139 193 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 139 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 139 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 139 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 139 193 (accept_3_3 29 139 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 139 193 (Polychromatic418967fa.accept_13_2_9_11_1_258 28 139 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 139 193
  (Polychromatic418967fa.accept_13_1_9_11_1_703 27 139 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 139 193 (accept_3_3 26 139 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 139 193 (Polychromatic418967fa.accept_15_10_4_13_1_4506 25 139 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 139 193 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 139 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 139 193 (accept_3_3 23 139 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 139 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 139 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 139 193
  (Polychromatic418967fa.accept_13_8_9_11_1_1265 21 139 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 139 193 (accept_3_3 20 139 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 139 193 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 139 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 139 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 139 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 139 193 (accept_3_3 17 139 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 139 193 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 139 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 139 193
  (Polychromatic418967fa.accept_13_2_9_11_1_258 15 139 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 139 193 (accept_3_3 14 139 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 139 193 (Polychromatic418967fa.accept_22_13_7_17_1_11231 13 139 193 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 139 193 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 139 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 139 193 (accept_3_3 11 139 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 139 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 139 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 139 193
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 139 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 139 193 (accept_3_3 8 139 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  139 193 (Polychromatic418967fa.accept_13_7_9_11_1_705 7 139 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 139 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 139 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 139 193 (accept_3_3 5 139 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 139 193 (Polychromatic418967fa.accept_10_4_9_3_1_1907 4 139 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 139 193
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 139 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 139 193 (accept_3_3 2 139 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  139 193 (Polychromatic418967fa.accept_11_1_7_6_1_378 1 139 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 139 193))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 138 193 (Eq.refl
  Bool.true) (allA_succ_of_accept 55 138 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 138 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 138 193
  (Polychromatic418967fa.accept_15_9_3_13_1_1686 54 138 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 138 193 (accept_3_3 53 138 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 138 193 (Polychromatic418967fa.accept_9_7_3_4_1_218 52 138 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 138 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 138 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 138 193 (accept_3_3 50 138 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 138 193 (Polychromatic418967fa.accept_13_10_8_11_1_1985 49 138 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 138 193
  (Polychromatic418967fa.accept_7_6_5_4_1_297 48 138 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 138 193 (accept_3_3 47 138 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 138 193 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 138 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 138 193 (Polychromatic418967fa.accept_10_5_8_3_1_229 45 138 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 138 193 (accept_3_3 44 138 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 138 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 138 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 138 193
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 138 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 138 193 (accept_3_3 41 138 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 138 193 (Polychromatic418967fa.accept_13_1_8_11_1_724 40 138 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 138 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 138 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 138 193 (accept_3_3 38 138 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 138 193 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 138 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 138 193
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 138 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 138 193 (accept_3_3 35 138 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 138 193 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 138 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 138 193 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 138 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 138 193 (accept_3_3 32 138 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 138 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 138 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 138 193
  (Polychromatic418967fa.accept_7_2_5_4_1_115 30 138 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 138 193 (accept_3_3 29 138 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 138 193 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 138 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 138 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 138 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 138 193 (accept_3_3 26 138 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 138 193 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 138 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 138 193
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 138 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 138 193 (accept_3_3 23 138 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 138 193 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 138 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 138 193 (Polychromatic418967fa.accept_10_1_8_3_1_947 21 138 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 138 193 (accept_3_3 20 138 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 138 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 138 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 138 193
  (Polychromatic418967fa.accept_17_1_2_6_1_818 18 138 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 138 193 (accept_3_3 17 138 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 138 193 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 138 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 138 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 138 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 138 193 (accept_3_3 14 138 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 138 193 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 138 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 138 193
  (Polychromatic418967fa.accept_15_12_3_13_1_4481 12 138 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 138 193 (accept_3_3 11 138 193 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 138 193 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 138 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 138 193 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 138 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 138 193 (accept_3_3 8 138 193
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 138 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 7
  138 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 138 193
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 138 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 138 193 (accept_3_3 5 138 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  138 193 (Polychromatic418967fa.accept_13_4_8_11_1_1937 4 138 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 138 193 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 138 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 138 193 (accept_3_3 2 138 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 138 193 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 138 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  193)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 137 193 (Eq.refl Bool.true) (allA_of_3_1 57
  137 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 58 136 193 (Eq.refl Bool.true) (allA_succ_of_accept 57
  136 193 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 136 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 136 193 (accept_3_3 56 136 193 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 136 193 (Polychromatic418967fa.accept_7_6_3_4_1_294 55 136 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 136 193 (Polychromatic418967fa.accept_22_10_4_17_1_7993 54 136
  193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 136 193 (accept_3_3 53 136
  193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 136 193
  (Polychromatic418967fa.accept_9_7_1_4_1_217 52 136 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 136 193 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 136 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 136 193 (accept_3_3 50 136 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 136 193 (Polychromatic418967fa.accept_10_9_6_3_1_545 49 136 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 136 193
  (Polychromatic418967fa.accept_7_6_3_4_1_294 48 136 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 136 193 (accept_3_3 47 136 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 136 193 (Polychromatic418967fa.accept_11_2_4_6_1_2412 46 136 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 136 193 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 136 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 136 193 (accept_3_3 44 136 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 136 193 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 136 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 136 193
  (Polychromatic418967fa.accept_9_6_1_4_1_474 42 136 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 136 193 (accept_3_3 41 136 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 136 193 (Polychromatic418967fa.accept_15_10_1_13_1_2609 40 136 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 136 193 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 136 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 136 193 (accept_3_3 38 136 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 136 193 (Polychromatic418967fa.accept_10_7_6_3_1_927 37 136 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 136 193
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 136 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 136 193 (accept_3_3 35 136 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 136 193 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 136 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 136 193 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 136 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 136 193 (accept_3_3 32 136 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 136 193 (Polychromatic418967fa.accept_13_5_6_11_1_1933 31 136 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 136 193
  (Polychromatic418967fa.accept_9_3_1_4_1_216 30 136 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 136 193 (accept_3_3 29 136 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 136 193 (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 136 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 136 193 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 136 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 136 193 (accept_3_3 26 136 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 136 193 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 136 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 136 193
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 136 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 136 193 (accept_3_3 23 136 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 136 193 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 136 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 136 193 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 136 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 136 193 (accept_3_3 20 136 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 136 193 (Polychromatic418967fa.accept_10_9_6_3_1_545 19 136 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 136 193
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 136 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 136 193 (accept_3_3 17 136 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 136 193 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 136 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 136 193 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 136 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 136 193 (accept_3_3 14 136 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 136 193 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 136 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 136 193
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 136 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 136 193 (accept_3_3 11 136 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 136 193 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 136 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 136 193 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 136 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 136 193 (accept_3_3 8 136 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 136 193 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 136 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 136 193
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 136 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 136 193 (accept_3_3 5 136 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  136 193 (Polychromatic418967fa.accept_13_4_6_11_1_2017 4 136 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 136 193 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 136 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 136 193 (accept_3_3 2 136 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 136 193 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 136 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 136
  193)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 135 193 (Eq.refl Bool.true)
  (allA_succ_of_accept 58 135 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 135 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 135 193 (Polychromatic418967fa.accept_10_7_5_3_1_542 57 135
  193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 135 193 (accept_3_3 56 135
  193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 135 193
  (Polychromatic418967fa.accept_7_6_2_4_1_291 55 135 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 135 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 135 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 135 193 (accept_3_3 53 135 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 135 193 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 135 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 135 193
  (Polychromatic418967fa.accept_20_11_15_13_1_8224 51 135 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 135 193 (accept_3_3 50 135 193 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 135 193 (Polychromatic418967fa.accept_19_11_2_3_1_8424 49 135 193 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 135 193 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 135 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 135 193 (accept_3_3 47 135 193
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 135 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 46
  135 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 135 193
  (Polychromatic418967fa.accept_12_9_3_1_1_303 45 135 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 135 193 (accept_3_3 44 135 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 135 193 (Polychromatic418967fa.accept_17_9_16_6_1_4820 43 135 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 135 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 135 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 135 193 (accept_3_3 41 135 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 135 193 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 135 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 135 193
  (Polychromatic418967fa.accept_18_3_9_13_1_1235 39 135 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 135 193 (accept_3_3 38 135 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 135 193 (Polychromatic418967fa.accept_10_7_5_3_1_542 37 135 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 135 193 (Polychromatic418967fa.accept_19_17_2_3_1_4190 36 135 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 135 193 (accept_3_3 35 135 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 135 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 135 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 135 193
  (Polychromatic418967fa.accept_7_5_2_4_1_126 33 135 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 135 193 (accept_3_3 32 135 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 135 193 (Polychromatic418967fa.accept_11_9_3_6_1_797 31 135 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 135 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 135 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 135 193 (accept_3_3 29 135 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 135 193 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 135 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 135 193
  (Polychromatic418967fa.accept_7_6_2_4_1_291 27 135 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 135 193 (accept_3_3 26 135 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 135 193 (Polychromatic418967fa.accept_19_6_2_3_1_11217 25 135 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 135 193 (Polychromatic418967fa.accept_16_8_7_1_1_8875 24 135 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 135 193 (accept_3_3 23 135 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 135 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 135 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 135 193
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 135 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 135 193 (accept_3_3 20 135 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 135 193 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 135 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 135 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 135 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 135 193 (accept_3_3 17 135 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 135 193 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 135 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 135 193
  (Polychromatic418967fa.accept_21_15_9_4_1_2207 15 135 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 135 193 (accept_3_3 14 135 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 135 193 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 135 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 135 193 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 135 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 135 193 (accept_3_3 11 135 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 135 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 135 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 135 193
  (Polychromatic418967fa.accept_11_9_3_6_1_797 9 135 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 135 193 (accept_3_3 8 135 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  135 193 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 135 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 135 193 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 135 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 135 193 (accept_3_3 5 135 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 135 193 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 135 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 135 193
  (Polychromatic418967fa.accept_13_3_5_11_1_716 3 135 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 135 193 (accept_3_3 2 135 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  135 193 (Polychromatic418967fa.accept_19_1_2_3_1_6995 1 135 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 135 193))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 134 193
  (Eq.refl Bool.true) (allA_of_3_1 60 134 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 61 133 193 (Eq.refl
  Bool.true) (allA_succ_of_accept 60 133 193 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 133 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 133 193 (accept_3_3 59 133 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 133 193 (Polychromatic418967fa.accept_17_7_14_6_1_4882 58 133 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 133 193
  (Polychromatic418967fa.accept_9_3_7_4_1_53 57 133 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 133 193 (accept_3_3 56 133 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 133 193 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 133 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 133 193 (Polychromatic418967fa.accept_13_2_3_11_1_1287 54 133 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 133 193 (accept_3_3 53 133 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 133 193 (Polychromatic418967fa.accept_8_4_5_1_1_299 52 133 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 133 193
  (Polychromatic418967fa.accept_9_6_7_4_1_212 51 133 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 133 193 (accept_3_3 50 133 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 133 193 (Polychromatic418967fa.accept_11_5_1_6_1_774 49 133 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 133 193 (Polychromatic418967fa.accept_9_3_7_4_1_53 48 133 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 133 193 (accept_3_3 47 133 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 133 193 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 133 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 133 193
  (Polychromatic418967fa.accept_14_3_7_11_1_765 45 133 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 133 193 (accept_3_3 44 133 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 133 193 (Polychromatic418967fa.accept_21_1_7_4_1_4947 43 133 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 133 193 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 133 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 133 193 (accept_3_3 41 133 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 133 193 (Polychromatic418967fa.accept_11_7_1_6_1_1281 40 133 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 133 193
  (Polychromatic418967fa.accept_9_3_7_4_1_53 39 133 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 133 193 (accept_3_3 38 133 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 133 193 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 133 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 133 193 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 133 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 133 193 (accept_3_3 35 133 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 133 193 (Polychromatic418967fa.accept_13_8_3_11_1_3467 34 133 193
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 133 193
  (Polychromatic418967fa.accept_9_6_7_4_1_212 33 133 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 133 193 (accept_3_3 32 133 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 133 193 (Polychromatic418967fa.accept_13_5_3_11_1_1288 31 133 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 133 193 (Polychromatic418967fa.accept_9_3_7_4_1_53 30 133 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 133 193 (accept_3_3 29 133 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 133 193 (Polychromatic418967fa.accept_8_4_5_1_1_299 28 133 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 133 193
  (Polychromatic418967fa.accept_11_5_1_6_1_774 27 133 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 133 193 (accept_3_3 26 133 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 133 193 (Polychromatic418967fa.accept_16_9_5_1_1_1259 25 133 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 133 193 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 133 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 133 193 (accept_3_3 23 133 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 133 193 (Polychromatic418967fa.accept_16_6_5_1_1_7761 22 133 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 133 193
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 133 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 133 193 (accept_3_3 20 133 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 133 193 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 133 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 133 193 (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 133 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 133 193 (accept_3_3 17 133 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 133 193 (Polychromatic418967fa.accept_11_5_1_6_1_774 16 133
  193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 133 193
  (Polychromatic418967fa.accept_9_6_7_4_1_212 15 133 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 133 193 (accept_3_3 14 133 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 133 193 (Polychromatic418967fa.accept_16_13_5_1_1_3017 13 133 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 133 193 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 133 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 133 193 (accept_3_3 11 133 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 133 193 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 133 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 133 193
  (Polychromatic418967fa.accept_16_9_5_1_1_1259 9 133 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 133 193 (accept_3_3 8 133 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  133 193 (Polychromatic418967fa.accept_11_7_1_6_1_1281 7 133 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 133 193 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 133 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 133 193 (accept_3_3 5 133 193 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 133 193 (Polychromatic418967fa.accept_8_4_5_1_1_299 4 133 193 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 133 193
  (Polychromatic418967fa.accept_9_3_7_4_1_53 3 133 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 133 193 (accept_3_3 2 133 193 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  133 193 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 133 193 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 133 193)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_193_segment_000))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


