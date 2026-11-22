-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch191
-- name    : Polychromatic418967fa_Branch191
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:20:27.95183+00:00
-- url     : https://prove2.me/theorems/14951adf-1fa4-453e-ab7a-824a3a4e465f
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch191_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_191 : allB 191 191 :=
  allB_succ' 2 190 191 (Eq.refl Bool.true) (allA_of_3_0 2 190 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  189 191 (Eq.refl Bool.true) (allA_succ_of_accept 2 189 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 189 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 189 191 (accept_3_2 1 189 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 189 191))) (allB_succ' 4 188 191 (Eq.refl Bool.true)
  (allA_succ_of_accept 3 188 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 188 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 188 191 (Polychromatic418967fa.accept_12_2_8_11_1_31 2 188 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 188 191 (accept_3_2 1 188 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 188 191)))) (allB_succ' 5 187 191 (Eq.refl Bool.true) (allA_of_3_0
  5 187 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 6 186 191 (Eq.refl Bool.true) (allA_succ_of_accept 5
  186 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 186 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 186 191 (accept_3_2 4 186 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 186 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 186 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 186 191 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 186 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 186 191 (accept_3_2 1 186 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186 191)))))) (allB_succ' 7 185 191 (Eq.refl Bool.true)
  (allA_succ_of_accept 6 185 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 185 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 185 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 185 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 185 191 (accept_3_2 4 185 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 185 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 3
  185 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 185 191
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 185 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 185 191 (accept_3_2 1 185 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 185 191)))))))
  (allB_succ' 8 184 191 (Eq.refl Bool.true) (allA_of_3_0 8 184 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  9 183 191 (Eq.refl Bool.true) (allA_succ_of_accept 8 183 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 183 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 183 191 (accept_3_2 7 183 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 183 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 6
  183 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 183 191
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 183 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 183 191 (accept_3_2 4 183 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  183 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 183 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 183 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 183 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 183 191 (accept_3_2 1 183 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 183 191))))))))) (allB_succ' 10 182 191 (Eq.refl Bool.true) (allA_succ_of_accept 9 182
  191 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 182 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 182 191 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 182 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 182 191 (accept_3_2 7 182 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 182 191 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 182 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 182 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 5
  182 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 182 191 (accept_3_2 4 182
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 182 191 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 182 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 182 191
  (Polychromatic418967fa.accept_11_2_6_4_1_3028 2 182 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 182 191 (accept_3_2 1 182 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 182
  191)))))))))) (allB_succ' 11 181 191 (Eq.refl Bool.true) (allA_of_3_0 11 181 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 180 191 (Eq.refl Bool.true) (allA_succ_of_accept 11 180 191
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 180 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 180 191 (accept_3_2 10 180 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  180 191 (Polychromatic418967fa.accept_21_9_12_2_1_4781 9 180 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 180 191 (Polychromatic418967fa.accept_13_8_11_9_1_593 8 180 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 180 191 (accept_3_2 7 180 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 180 191 (Polychromatic418967fa.accept_17_6_10_4_1_6007 6 180 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 180 191
  (Polychromatic418967fa.accept_16_5_4_15_1_1102 5 180 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 180 191 (accept_3_2 4 180 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  180 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 180 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 180 191 (Polychromatic418967fa.accept_13_2_11_9_1_591 2 180 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 180 191 (accept_3_2 1 180 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 180 191)))))))))))) (allB_succ' 13 179 191 (Eq.refl Bool.true) (allA_succ_of_accept 12
  179 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 179 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 179 191 (Polychromatic418967fa.accept_16_11_3_15_1_1989 11 179 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 179 191 (accept_3_2 10 179 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 179 191 (Polychromatic418967fa.accept_19_9_8_1_1_11103 9 179
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 179 191
  (Polychromatic418967fa.accept_10_8_9_1_1_189 8 179 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 179 191 (accept_3_2 7 179 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  179 191 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 179 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 179 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 179 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 179 191 (accept_3_2 4 179 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 179 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 179 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 179 191
  (Polychromatic418967fa.accept_10_2_9_1_1_185 2 179 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 179 191 (accept_3_2 1 179 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 179
  191))))))))))))) (allB_succ' 14 178 191 (Eq.refl Bool.true) (allA_of_3_0 14 178 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 177 191 (Eq.refl Bool.true) (allA_succ_of_accept 14 177 191
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 177 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 177 191 (accept_3_2 13 177 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 177 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 177 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 177 191 (Polychromatic418967fa.accept_13_11_8_9_1_1161 11 177 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 177 191 (accept_3_2 10 177 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 177 191 (Polychromatic418967fa.accept_18_9_15_11_1_5693 9 177
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 177 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 177 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 177 191 (accept_3_2 7 177 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  177 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 177 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 177 191 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 177 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 177 191 (accept_3_2 4 177 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 177 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 177 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 177 191
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 177 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 177 191 (accept_3_2 1 177 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 177
  191))))))))))))))) (allB_succ' 16 176 191 (Eq.refl Bool.true) (allA_succ_of_accept 15 176 191
  (Polychromatic418967fa.accept_6_3_2_5_1_32 15 176 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 176 191 (Polychromatic418967fa.accept_12_2_8_11_1_31 14 176 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 176 191 (accept_3_2 13 176 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 176 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 176 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 176 191 (Polychromatic418967fa.accept_13_11_7_9_1_612
  11 176 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 176 191 (accept_3_2 10
  176 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 176 191
  (Polychromatic418967fa.accept_6_3_2_5_1_32 9 176 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 176 191 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 176 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 176 191 (accept_3_2 7 176 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 176 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 176 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 176 191 (Polychromatic418967fa.accept_10_5_6_1_1_836 5
  176 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 176 191 (accept_3_2 4 176
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 176 191 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 176 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 176 191
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 176 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 176 191 (accept_3_2 1 176 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 176
  191)))))))))))))))) (allB_succ' 17 175 191 (Eq.refl Bool.true) (allA_of_3_0 17 175 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 18 174 191 (Eq.refl Bool.true) (allA_succ_of_accept 17 174 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 174 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 174 191 (accept_3_2 16 174 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 174 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 174 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 174 191 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 174 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 174 191 (accept_3_2 13 174 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 174 191 (Polychromatic418967fa.accept_21_12_6_2_1_7950 12 174 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 174 191
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 174 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 174 191 (accept_3_2 10 174 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  174 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 174 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 174 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 174 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 174 191 (accept_3_2 7 174 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 174 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 174 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 174 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 174 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 174 191 (accept_3_2 4 174 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  174 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 174 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 174 191 (Polychromatic418967fa.accept_11_2_9_4_1_310 2 174 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 174 191 (accept_3_2 1 174 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 174 191)))))))))))))))))) (allB_succ' 19 173 191 (Eq.refl Bool.true)
  (allA_succ_of_accept 18 173 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 173 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 173 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 173 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 173 191 (accept_3_2 16 173 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 173 191
  (Polychromatic418967fa.accept_19_15_2_1_1_2822 15 173 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 173 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 173 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 173 191 (accept_3_2 13 173 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 173 191 (Polychromatic418967fa.accept_10_2_3_1_1_481 12 173 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 173 191
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 173 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 173 191 (accept_3_2 10 173 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  173 191 (Polychromatic418967fa.accept_19_9_2_1_1_2821 9 173 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 173 191 (Polychromatic418967fa.accept_10_8_3_1_1_1316 8 173 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 173 191 (accept_3_2 7 173 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 173 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 173 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 173 191
  (Polychromatic418967fa.accept_13_5_4_9_1_601 5 173 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 173 191 (accept_3_2 4 173 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  173 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 173 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 173 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 173 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 173 191 (accept_3_2 1 173 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 173 191))))))))))))))))))) (allB_succ' 20 172 191 (Eq.refl Bool.true) (allA_of_3_0 20
  172 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 21 171 191 (Eq.refl Bool.true) (allA_succ_of_accept 20
  171 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 171 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 171 191 (accept_3_2 19 171 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 171 191 (Polychromatic418967fa.accept_13_5_2_9_1_1195 18 171 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 171 191 (Polychromatic418967fa.accept_15_2_6_11_1_1587 17 171
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 171 191 (accept_3_2 16 171
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 171 191
  (Polychromatic418967fa.accept_7_1_3_2_1_13 15 171 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 171 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 171 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 171 191 (accept_3_2 13 171 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 171 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 171 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 171 191
  (Polychromatic418967fa.accept_13_11_2_9_1_2640 11 171 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 171 191 (accept_3_2 10 171 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  171 191 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 171 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 171 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 171 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 191 (accept_3_2 7 171 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 171 191 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 171 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 171 191
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 171 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 171 191 (accept_3_2 4 171 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  171 191 (Polychromatic418967fa.accept_13_3_2_9_1_1187 3 171 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 171 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 171 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 191 (accept_3_2 1 171 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 171 191))))))))))))))))))))) (allB_succ' 22 170 191 (Eq.refl Bool.true)
  (allA_succ_of_accept 21 170 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 170 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 170 191 (Polychromatic418967fa.accept_12_8_2_11_1_246 20 170
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 170 191 (accept_3_2 19 170
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 170 191
  (Polychromatic418967fa.accept_13_5_1_9_1_618 18 170 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 170 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 170 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 170 191 (accept_3_2 16 170 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 170 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 170 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 170 191 (Polychromatic418967fa.accept_9_5_8_2_1_409
  14 170 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 170 191 (accept_3_2 13
  170 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 170 191
  (Polychromatic418967fa.accept_9_3_8_2_1_162 12 170 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 170 191 (Polychromatic418967fa.accept_13_11_1_9_1_1179 11 170 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 170 191 (accept_3_2 10 170 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 170 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 170 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 170 191 (Polychromatic418967fa.accept_12_8_2_11_1_246
  8 170 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 170 191 (accept_3_2 7
  170 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 170 191
  (Polychromatic418967fa.accept_9_6_8_2_1_410 6 170 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 170 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 170 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 170 191 (accept_3_2 4 170 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 170 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 170 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 170 191 (Polychromatic418967fa.accept_13_2_1_9_1_1174
  2 170 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 170 191 (accept_3_2 1
  170 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 170 191)))))))))))))))))))))) (allB_succ' 23 169 191
  (Eq.refl Bool.true) (allA_of_3_0 23 169 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 168 191 (Eq.refl
  Bool.true) (allA_succ_of_accept 23 168 191 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 168 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 168 191 (accept_3_2 22 168 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 168 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 168 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 168 191
  (Polychromatic418967fa.accept_16_4_8_15_1_1113 20 168 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 168 191 (accept_3_2 19 168 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 168 191 (Polychromatic418967fa.accept_11_7_3_4_1_729 18 168 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 168 191 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 168 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 168 191 (accept_3_2 16 168 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 168 191 (Polychromatic418967fa.accept_18_15_6_11_1_5651 15 168 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 168 191
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 168 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 168 191 (accept_3_2 13 168 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 168 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 168 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 168 191 (Polychromatic418967fa.accept_17_11_15_4_1_2415 11 168 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 168 191 (accept_3_2 10 168 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 168 191 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 168 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 168 191
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 168 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 168 191 (accept_3_2 7 168 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  168 191 (Polychromatic418967fa.accept_15_6_3_11_1_848 6 168 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 168 191 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 168 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 168 191 (accept_3_2 4 168 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 168 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 168 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 168 191
  (Polychromatic418967fa.accept_17_2_15_4_1_4723 2 168 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 168 191 (accept_3_2 1 168 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 168
  191)))))))))))))))))))))))) (allB_succ' 25 167 191 (Eq.refl Bool.true) (allA_succ_of_accept 24 167 191
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 167 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 167 191 (Polychromatic418967fa.accept_19_4_15_1_1_2819 23 167 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 167 191 (accept_3_2 22 167 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 167 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 167 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 167 191 (Polychromatic418967fa.accept_11_9_2_4_1_707
  20 167 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 167 191 (accept_3_2 19
  167 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 167 191
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 167 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 167 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 167 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 167 191 (accept_3_2 16 167 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 167 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 167 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 167 191 (Polychromatic418967fa.accept_10_4_7_1_1_471
  14 167 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 167 191 (accept_3_2 13
  167 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 167 191
  (Polychromatic418967fa.accept_9_3_5_2_1_28 12 167 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 167 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 167 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 167 191 (accept_3_2 10 167 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 167 191 (Polychromatic418967fa.accept_11_9_2_4_1_707 9 167 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 167 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 8
  167 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 167 191 (accept_3_2 7 167
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 167 191
  (Polychromatic418967fa.accept_9_6_5_2_1_421 6 167 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 167 191 (Polychromatic418967fa.accept_15_5_2_11_1_1596 5 167 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 167 191 (accept_3_2 4 167 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 167 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 167 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 167 191 (Polychromatic418967fa.accept_13_2_11_9_1_591
  2 167 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 167 191 (accept_3_2 1
  167 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 167 191))))))))))))))))))))))))) (allB_succ' 26 166 191
  (Eq.refl Bool.true) (allA_of_3_0 26 166 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 27 165 191 (Eq.refl
  Bool.true) (allA_succ_of_accept 26 165 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 165 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 165 191 (accept_3_2 25 165 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 165 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 165 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 165 191
  (Polychromatic418967fa.accept_9_5_3_2_1_171 23 165 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 165 191 (accept_3_2 22 165 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 165 191 (Polychromatic418967fa.accept_19_2_13_1_1_6831 21 165 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 165 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 165 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 165 191 (accept_3_2 19 165 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 165 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 165 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 165 191
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 165 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 165 191 (accept_3_2 16 165 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 165 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 165 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 165 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 165 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 165 191 (accept_3_2 13 165 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 165 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 165 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 165 191
  (Polychromatic418967fa.accept_23_11_4_7_1_11102 11 165 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 165 191 (accept_3_2 10 165 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 165 191 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 165 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 165 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 165 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 191 (accept_3_2 7 165 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 165 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 6
  165 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 165 191
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 165 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 165 191 (accept_3_2 4 165 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  165 191 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 165 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 165 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 165 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 191 (accept_3_2 1 165 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 165 191))))))))))))))))))))))))))) (allB_succ' 28 164 191 (Eq.refl Bool.true)
  (allA_succ_of_accept 27 164 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 164 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 164 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 164 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 164 191 (accept_3_2 25 164 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 164 191
  (Polychromatic418967fa.accept_13_11_8_9_1_1161 24 164 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 164 191 (Polychromatic418967fa.accept_17_6_11_4_1_1525 23 164 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 164 191 (accept_3_2 22 164 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 164 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 164 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 164 191 (Polychromatic418967fa.accept_7_6_3_2_1_461
  20 164 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 164 191 (accept_3_2 19
  164 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 164 191
  (Polychromatic418967fa.accept_15_3_14_11_1_1579 18 164 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 164 191 (Polychromatic418967fa.accept_10_7_4_1_1_1319 17 164 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 164 191 (accept_3_2 16 164 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 164 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 164 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 164 191
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 164 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 164 191 (accept_3_2 13 164 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 164 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 164 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 164 191 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 164 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 164 191 (accept_3_2 10 164 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 164 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 164 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 164 191
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 164 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 164 191 (accept_3_2 7 164 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  164 191 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 164 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 164 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 164 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 164 191 (accept_3_2 4 164 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 164 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 164 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 164 191
  (Polychromatic418967fa.accept_12_2_8_11_1_31 2 164 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 164 191 (accept_3_2 1 164 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 164
  191)))))))))))))))))))))))))))) (allB_succ' 29 163 191 (Eq.refl Bool.true) (allA_of_3_0 29 163 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 30 162 191 (Eq.refl Bool.true) (allA_succ_of_accept 29 162 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 162 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 162 191 (accept_3_2 28 162 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 162 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 162 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 162 191 (Polychromatic418967fa.accept_10_6_2_1_1_494 26 162 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 162 191 (accept_3_2 25 162 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 162 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 162 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 162 191
  (Polychromatic418967fa.accept_10_3_2_1_1_839 23 162 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 162 191 (accept_3_2 22 162 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 162 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 162 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 162 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 162 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 162 191 (accept_3_2 19 162 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 162 191 (Polychromatic418967fa.accept_11_7_8_4_1_718 18 162 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 162 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 162 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 162 191 (accept_3_2 16 162 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 162 191 (Polychromatic418967fa.accept_13_2_6_9_1_2636 15 162 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 162 191 (Polychromatic418967fa.accept_13_1_6_9_1_1197 14 162 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 162 191 (accept_3_2 13 162 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 162 191 (Polychromatic418967fa.accept_11_1_8_4_1_717 12 162
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 162 191
  (Polychromatic418967fa.accept_19_11_10_1_1_2773 11 162 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 162 191 (accept_3_2 10 162 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 162 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 162 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 162 191 (Polychromatic418967fa.accept_15_8_12_11_1_1570 8 162
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 162 191 (accept_3_2 7 162 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 162 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 6
  162 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 162 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 162 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 162 191 (accept_3_2 4 162 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  162 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 162 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 162 191 (Polychromatic418967fa.accept_13_2_6_9_1_2636 2 162 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 162 191 (accept_3_2 1 162 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 162 191)))))))))))))))))))))))))))))) (allB_succ' 31 161 191 (Eq.refl Bool.true)
  (allA_succ_of_accept 30 161 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 161 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 161 191 (Polychromatic418967fa.accept_13_3_5_9_1_5285 29 161
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 161 191 (accept_3_2 28 161
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 161 191
  (Polychromatic418967fa.accept_13_1_5_9_1_226 27 161 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 161 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 161 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 161 191 (accept_3_2 25 161 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 161 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 161 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 161 191 (Polychromatic418967fa.accept_9_5_8_2_1_409
  23 161 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 161 191 (accept_3_2 22
  161 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 161 191
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 161 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 161 191 (Polychromatic418967fa.accept_18_2_17_11_1_3178 20 161 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 161 191 (accept_3_2 19 161 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 161 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 161 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 161 191
  (Polychromatic418967fa.accept_13_4_5_9_1_1829 17 161 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 161 191 (accept_3_2 16 161 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 161 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 161 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 161 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 161 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 161 191 (accept_3_2 13 161 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 161 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 161 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 161 191
  (Polychromatic418967fa.accept_16_11_1_15_1_1123 11 161 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 161 191 (accept_3_2 10 161 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 161 191 (Polychromatic418967fa.accept_21_9_14_2_1_6370 9 161 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 161 191 (Polychromatic418967fa.accept_11_8_7_4_1_3011 8 161 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 161 191 (accept_3_2 7 161 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 161 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 6
  161 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 161 191
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 161 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 161 191 (accept_3_2 4 161 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  161 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 161 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 161 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 161 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 161 191 (accept_3_2 1 161 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 161 191))))))))))))))))))))))))))))))) (allB_succ' 32 160 191 (Eq.refl Bool.true)
  (allA_of_3_0 32 160 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 159 191 (Eq.refl Bool.true)
  (allA_succ_of_accept 32 159 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 159 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 159 191 (accept_3_2 31 159 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 159 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 159 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 159 191
  (Polychromatic418967fa.accept_19_10_7_1_1_1685 29 159 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 159 191 (accept_3_2 28 159 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 159 191 (Polychromatic418967fa.accept_17_10_6_4_1_2506 27 159 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 159 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 159 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 159 191 (accept_3_2 25 159 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 159 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 159 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 159 191
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 159 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 159 191 (accept_3_2 22 159 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 159 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 159 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 159 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 159 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 159 191 (accept_3_2 19 159 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 159 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 159 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 159 191
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 159 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 159 191 (accept_3_2 16 159 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 159 191 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 159 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 159 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 159 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 191 (accept_3_2 13 159 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 159 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 159 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 159 191
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 159 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 159 191 (accept_3_2 10 159 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  159 191 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 159 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 159 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 159 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 191 (accept_3_2 7 159 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 159 191 (Polychromatic418967fa.accept_13_6_3_9_1_1827 6 159 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 159 191
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 159 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 159 191 (accept_3_2 4 159 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  159 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 159 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 159 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 159 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 191 (accept_3_2 1 159 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 159 191))))))))))))))))))))))))))))))))) (allB_succ' 34 158 191 (Eq.refl Bool.true)
  (allA_succ_of_accept 33 158 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 158 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 158 191 (Polychromatic418967fa.accept_12_8_2_11_1_246 32 158
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 158 191 (accept_3_2 31 158
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 158 191
  (Polychromatic418967fa.accept_9_3_5_2_1_28 30 158 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 158 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 158 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 158 191 (accept_3_2 28 158 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 158 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 158 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 158 191 (Polychromatic418967fa.accept_7_5_4_2_1_235
  26 158 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 158 191 (accept_3_2 25
  158 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 158 191
  (Polychromatic418967fa.accept_9_6_5_2_1_421 24 158 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 158 191 (Polychromatic418967fa.accept_10_3_8_1_1_182 23 158 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 158 191 (accept_3_2 22 158 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 158 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 158 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 158 191 (Polychromatic418967fa.accept_7_6_4_2_1_236
  20 158 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 158 191 (accept_3_2 19
  158 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 158 191
  (Polychromatic418967fa.accept_13_5_2_9_1_1195 18 158 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 158 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 158 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 158 191 (accept_3_2 16 158 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 158 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 158 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 158 191 (Polychromatic418967fa.accept_13_1_2_9_1_1186
  14 158 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 158 191 (accept_3_2 13
  158 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 158 191
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 158 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 158 191 (Polychromatic418967fa.accept_13_11_2_9_1_2640 11 158 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 158 191 (accept_3_2 10 158 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 158 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 158 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 158 191 (Polychromatic418967fa.accept_9_8_5_2_1_422 8
  158 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 158 191 (accept_3_2 7 158
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 158 191
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 158 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 158 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 158 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 158 191 (accept_3_2 4 158 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 158 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 158 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 158 191 (Polychromatic418967fa.accept_14_2_4_9_1_2121
  2 158 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 158 191 (accept_3_2 1
  158 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158 191)))))))))))))))))))))))))))))))))) (allB_succ' 35
  157 191 (Eq.refl Bool.true) (allA_of_3_0 35 157 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 156 191
  (Eq.refl Bool.true) (allA_succ_of_accept 35 156 191 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 156 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 156 191 (accept_3_2 34 156 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 156 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 156 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 156 191
  (Polychromatic418967fa.accept_9_5_3_2_1_171 32 156 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 156 191 (accept_3_2 31 156 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 156 191 (Polychromatic418967fa.accept_17_13_3_4_1_2537 30 156 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 156 191 (Polychromatic418967fa.accept_16_13_12_15_1_6290 29 156 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 156 191 (accept_3_2 28 156 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 156 191 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 156 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 156 191
  (Polychromatic418967fa.accept_9_8_3_2_1_417 26 156 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 156 191 (accept_3_2 25 156 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 156 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 156 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 156 191 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 156 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 156 191 (accept_3_2 22 156 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 156 191 (Polychromatic418967fa.accept_14_7_2_9_1_2093 21 156 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 156 191
  (Polychromatic418967fa.accept_11_9_2_4_1_707 20 156 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 156 191 (accept_3_2 19 156 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 156 191 (Polychromatic418967fa.accept_14_4_2_9_1_2092 18 156 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 156 191 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 156 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 156 191 (accept_3_2 16 156 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 156 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 156 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 156 191
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 156 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 156 191 (accept_3_2 13 156 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 156 191 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 156 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 156 191 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 156 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 156 191 (accept_3_2 10 156 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 156 191 (Polychromatic418967fa.accept_11_9_2_4_1_707 9 156 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 156 191
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 156 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 156 191 (accept_3_2 7 156 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  156 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 156 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 156 191 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 156 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 156 191 (accept_3_2 4 156 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 156 191 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 156 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 156 191
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 156 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 156 191 (accept_3_2 1 156 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156
  191)))))))))))))))))))))))))))))))))))) (allB_succ' 37 155 191 (Eq.refl Bool.true) (allA_succ_of_accept 36 155 191
  (Polychromatic418967fa.accept_8_4_3_7_1_491 36 155 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 155 191 (Polychromatic418967fa.accept_16_3_11_15_1_1963 35 155 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 155 191 (accept_3_2 34 155 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 155 191 (Polychromatic418967fa.accept_16_1_11_15_1_498 33 155 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 155 191
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 32 155 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 155 191 (accept_3_2 31 155 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 155 191 (Polychromatic418967fa.accept_11_8_1_4_1_2318 30 155 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 155 191 (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 155 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 155 191 (accept_3_2 28 155 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 155 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 155 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 155 191
  (Polychromatic418967fa.accept_10_6_5_1_1_482 26 155 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 155 191 (accept_3_2 25 155 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 155 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 155 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 155 191 (Polychromatic418967fa.accept_13_10_12_9_1_1837 23 155 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 155 191 (accept_3_2 22 155 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 155 191 (Polychromatic418967fa.accept_13_8_12_9_1_1168 21 155
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 155 191
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 155 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 155 191 (accept_3_2 19 155 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 155 191 (Polychromatic418967fa.accept_27_18_20_2_1_9103 18 155 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 155 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 155 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 155 191 (accept_3_2 16 155 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 155 191 (Polychromatic418967fa.accept_17_15_2_4_1_2423 15 155 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 155 191
  (Polychromatic418967fa.accept_10_4_5_1_1_497 14 155 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 155 191 (accept_3_2 13 155 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 155 191 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 155 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 155 191 (Polychromatic418967fa.accept_19_11_3_1_1_2799 11 155 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 155 191 (accept_3_2 10 155 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 155 191 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 155 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 155 191
  (Polychromatic418967fa.accept_11_8_1_4_1_2318 8 155 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 155 191 (accept_3_2 7 155 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  155 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 155 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 155 191 (Polychromatic418967fa.accept_19_5_3_1_1_4055 5 155 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 155 191 (accept_3_2 4 155 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 155 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 155 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 155 191
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 2 155 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 155 191 (accept_3_2 1 155 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 155
  191))))))))))))))))))))))))))))))))))))) (allB_succ' 38 154 191 (Eq.refl Bool.true) (allA_of_3_0 38 154 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 153 191 (Eq.refl Bool.true) (allA_succ_of_accept 38 153 191
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 153 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 153 191 (accept_3_2 37 153 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 153 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 153 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 153 191 (Polychromatic418967fa.accept_20_15_13_11_1_5110 35 153 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 153 191 (accept_3_2 34 153 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 153 191 (Polychromatic418967fa.accept_18_15_9_11_1_4371 33 153
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 153 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 153 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 153 191 (accept_3_2 31 153 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 153 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 153 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 153 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 153 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 153 191 (accept_3_2 28 153 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 153 191 (Polychromatic418967fa.accept_11_5_10_4_1_1157 27 153 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 153 191
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 153 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 153 191 (accept_3_2 25 153 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 153 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 153 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 153 191 (Polychromatic418967fa.accept_15_8_3_11_1_849 23 153 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 153 191 (accept_3_2 22 153 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 153 191 (Polychromatic418967fa.accept_15_6_3_11_1_848 21 153
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 153 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 153 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 153 191 (accept_3_2 19 153 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 153 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 153 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 153 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 153 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 153 191 (accept_3_2 16 153 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 153 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 153 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 153 191
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 153 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 153 191 (accept_3_2 13 153 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 153 191 (Polychromatic418967fa.accept_10_2_3_1_1_481 12 153 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 153 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 153 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 153 191 (accept_3_2 10 153 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 153 191 (Polychromatic418967fa.accept_21_9_6_2_1_3357 9 153 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 153 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 153 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 153 191 (accept_3_2 7 153 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  153 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 153 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 153 191 (Polychromatic418967fa.accept_11_5_10_4_1_1157 5 153 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 191 (accept_3_2 4 153 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 153 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 153 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 153 191
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 153 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 153 191 (accept_3_2 1 153 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 153
  191))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 152 191 (Eq.refl Bool.true) (allA_succ_of_accept 39 152 191
  (Polychromatic418967fa.accept_6_3_2_5_1_32 39 152 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 152 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 152 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 152 191 (accept_3_2 37 152 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 152 191 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 152 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 152 191
  (Polychromatic418967fa.accept_11_2_9_4_1_310 35 152 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 152 191 (accept_3_2 34 152 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 152 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 152 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 152 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 152 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 152 191 (accept_3_2 31 152 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 152 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 152 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 152 191
  (Polychromatic418967fa.accept_10_9_2_1_1_840 29 152 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 152 191 (accept_3_2 28 152 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 152 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 152 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 152 191 (Polychromatic418967fa.accept_10_6_2_1_1_494 26 152 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 152 191 (accept_3_2 25 152 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 152 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 152 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 152 191
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 152 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 152 191 (accept_3_2 22 152 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 152 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 152 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 152 191 (Polychromatic418967fa.accept_15_5_2_11_1_1596 20 152 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 152 191 (accept_3_2 19 152 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 152 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 152 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 152 191
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 152 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 152 191 (accept_3_2 16 152 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 152 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 152 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 152 191 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 152 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 152 191 (accept_3_2 13 152 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 152 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 152 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 152 191
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 152 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 152 191 (accept_3_2 10 152 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  152 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 152 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 152 191 (Polychromatic418967fa.accept_21_8_5_2_1_8004 8 152 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 152 191 (accept_3_2 7 152 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 152 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 152 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 152 191
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 152 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 152 191 (accept_3_2 4 152 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  152 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 152 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 152 191 (Polychromatic418967fa.accept_11_2_9_4_1_310 2 152 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 152 191 (accept_3_2 1 152 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 152 191)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 151 191 (Eq.refl
  Bool.true) (allA_of_3_0 41 151 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 150 191 (Eq.refl Bool.true)
  (allA_succ_of_accept 41 150 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 150 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 150 191 (accept_3_2 40 150 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 150 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 150 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 150 191
  (Polychromatic418967fa.accept_21_17_3_2_1_2111 38 150 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 150 191 (accept_3_2 37 150 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 150 191 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 150 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 150 191 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 150 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 150 191 (accept_3_2 34 150 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 150 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 150 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 150 191
  (Polychromatic418967fa.accept_9_5_6_2_1_161 32 150 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 150 191 (accept_3_2 31 150 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 150 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 150 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 150 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 150 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 150 191 (accept_3_2 28 150 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 150 191 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 150 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 150 191
  (Polychromatic418967fa.accept_7_5_3_2_1_249 26 150 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 150 191 (accept_3_2 25 150 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 150 191 (Polychromatic418967fa.accept_13_11_7_9_1_612 24 150 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 150 191 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 150 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 150 191 (accept_3_2 22 150 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 150 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 150 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 150 191
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 150 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 150 191 (accept_3_2 19 150 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 150 191 (Polychromatic418967fa.accept_17_1_14_4_1_1550 18 150 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 150 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 150 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 150 191 (accept_3_2 16 150 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 150 191 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 150 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 150 191
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 150 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 150 191 (accept_3_2 13 150 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 150 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 150 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 150 191 (Polychromatic418967fa.accept_13_11_7_9_1_612 11 150 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 150 191 (accept_3_2 10 150 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 150 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 150 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 150 191
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 150 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 150 191 (accept_3_2 7 150 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  150 191 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 150 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 150 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 150 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 150 191 (accept_3_2 4 150 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 150 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 150 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 150 191
  (Polychromatic418967fa.accept_13_2_7_9_1_2616 2 150 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 150 191 (accept_3_2 1 150 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  191)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 149 191 (Eq.refl Bool.true) (allA_succ_of_accept 42 149
  191 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 149 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 149 191 (Polychromatic418967fa.accept_13_2_6_9_1_2636 41 149 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 149 191 (accept_3_2 40 149 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 149 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 149 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 149 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 38
  149 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 149 191 (accept_3_2 37
  149 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 149 191
  (Polychromatic418967fa.accept_13_10_6_9_1_1152 36 149 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 149 191 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 149 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 149 191 (accept_3_2 34 149 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 149 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 149 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 149 191 (Polychromatic418967fa.accept_10_2_9_1_1_185
  32 149 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 149 191 (accept_3_2 31
  149 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 149 191
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 149 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 149 191 (Polychromatic418967fa.accept_13_3_6_9_1_1150 29 149 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 149 191 (accept_3_2 28 149 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 149 191 (Polychromatic418967fa.accept_13_1_6_9_1_1197 27 149 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 149 191
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 149 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 149 191 (accept_3_2 25 149 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 149 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 149 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 149 191 (Polychromatic418967fa.accept_13_10_6_9_1_1152 23 149 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 149 191 (accept_3_2 22 149 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 149 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 149 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 149 191
  (Polychromatic418967fa.accept_13_7_6_9_1_1831 20 149 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 149 191 (accept_3_2 19 149 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 149 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 149 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 149 191 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 149 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 149 191 (accept_3_2 16 149 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 149 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 149 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 149 191
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 149 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 149 191 (accept_3_2 13 149 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 149 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 149 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 149 191 (Polychromatic418967fa.accept_22_11_17_15_1_9500 11 149 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 149 191 (accept_3_2 10 149 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 149 191 (Polychromatic418967fa.accept_17_9_13_4_1_2408 9 149
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 149 191
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 149 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 149 191 (accept_3_2 7 149 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  149 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 149 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 149 191 (Polychromatic418967fa.accept_10_5_9_1_1_187 5 149 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 149 191 (accept_3_2 4 149 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 149 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 149 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 149 191
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 149 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 149 191 (accept_3_2 1 149 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 149
  191))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 148 191 (Eq.refl Bool.true) (allA_of_3_0 44 148 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 147 191 (Eq.refl Bool.true) (allA_succ_of_accept 44 147 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 147 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 147 191 (accept_3_2 43 147 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 147 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 147 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 147 191 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 147 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 147 191 (accept_3_2 40 147 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 147 191 (Polychromatic418967fa.accept_16_7_3_15_1_2940 39 147 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 147 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 147 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 147 191 (accept_3_2 37 147 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 147 191 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 147 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 147 191 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 147 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 147 191 (accept_3_2 34 147 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 147 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 147 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 147 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 147 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 147 191 (accept_3_2 31 147 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 147 191 (Polychromatic418967fa.accept_14_2_7_9_1_2937 30 147 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 147 191 (Polychromatic418967fa.accept_15_14_12_11_1_1572 29 147 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 147 191 (accept_3_2 28 147 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 147 191 (Polychromatic418967fa.accept_16_11_3_15_1_1989 27 147
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 147 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 147 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 147 191 (accept_3_2 25 147 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 147 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 147 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 147 191 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 147 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 147 191 (accept_3_2 22 147 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 147 191 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 147 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 147 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 147 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 147 191 (accept_3_2 19 147 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 147 191 (Polychromatic418967fa.accept_13_5_4_9_1_601 18 147 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 147 191 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 147 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 147 191 (accept_3_2 16 147 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 147 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 147 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 147 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 147 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 147 191 (accept_3_2 13 147 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 147 191 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 147 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 147 191 (Polychromatic418967fa.accept_16_11_3_15_1_1989 11 147 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 147 191 (accept_3_2 10 147 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 147 191 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 147
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 147 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 147 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 147 191 (accept_3_2 7 147 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  147 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 147 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 147 191 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 147 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 147 191 (accept_3_2 4 147 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 147 191 (Polychromatic418967fa.accept_26_3_17_9_1_11101 3 147 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 147 191
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 147 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 147 191 (accept_3_2 1 147 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 147
  191))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 146 191 (Eq.refl Bool.true) (allA_succ_of_accept 45
  146 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 146 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 146 191 (Polychromatic418967fa.accept_12_8_2_11_1_246 44 146 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 146 191 (accept_3_2 43 146 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 146 191 (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 146
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 146 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 146 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 146 191 (accept_3_2 40 146 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 146 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 146 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 146 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 38 146 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 146 191 (accept_3_2 37 146 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 146 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 146 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 146 191
  (Polychromatic418967fa.accept_10_5_6_1_1_836 35 146 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 146 191 (accept_3_2 34 146 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 146 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 146 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 146 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 146 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 146 191 (accept_3_2 31 146 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 146 191 (Polychromatic418967fa.accept_21_9_20_2_1_8000 30 146 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 146 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 146 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 146 191 (accept_3_2 28 146 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 146 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 146 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 146 191 (Polychromatic418967fa.accept_19_7_13_1_1_6804 26 146 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 146 191 (accept_3_2 25 146 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 146 191 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 146 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 146 191
  (Polychromatic418967fa.accept_17_6_10_4_1_6007 23 146 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 146 191 (accept_3_2 22 146 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 146 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 146 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 146 191 (Polychromatic418967fa.accept_12_8_2_11_1_246 20 146 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 146 191 (accept_3_2 19 146 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 146 191 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 146 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 146 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 146 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 146 191 (accept_3_2 16 146 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 146 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 146 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 146 191 (Polychromatic418967fa.accept_18_14_2_11_1_4384 14 146 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 146 191 (accept_3_2 13 146 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 146 191 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 146
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 146 191
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 146 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 146 191 (accept_3_2 10 146 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  146 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 146 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 146 191 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 146 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 146 191 (accept_3_2 7 146 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 146 191 (Polychromatic418967fa.accept_13_6_3_9_1_1827 6 146 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 146 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 146 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 146 191 (accept_3_2 4 146 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  146 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 146 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 146 191 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 146 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 146 191 (accept_3_2 1 146 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 146 191)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 145 191 (Eq.refl
  Bool.true) (allA_of_3_0 47 145 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 144 191 (Eq.refl Bool.true)
  (allA_succ_of_accept 47 144 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 144 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 144 191 (accept_3_2 46 144 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 144 191 (Polychromatic418967fa.accept_10_5_4_1_1_842 45 144 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 144 191
  (Polychromatic418967fa.accept_13_5_1_9_1_618 44 144 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 144 191 (accept_3_2 43 144 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 144 191 (Polychromatic418967fa.accept_25_17_19_16_1_11100 42 144 191 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 41 144 191 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 144 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 144 191 (accept_3_2 40 144 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 144 191 (Polychromatic418967fa.accept_26_13_14_9_1_11099 39
  144 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 144 191
  (Polychromatic418967fa.accept_27_11_9_2_1_3160 38 144 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 144 191 (accept_3_2 37 144 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 144 191 (Polychromatic418967fa.accept_13_10_1_9_1_3380 36 144 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 144 191 (Polychromatic418967fa.accept_10_5_4_1_1_842 35 144 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 144 191 (accept_3_2 34 144 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 144 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 144 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 144 191
  (Polychromatic418967fa.accept_13_6_1_9_1_619 32 144 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 144 191 (accept_3_2 31 144 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 144 191 (Polychromatic418967fa.accept_11_8_1_4_1_2318 30 144 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 144 191 (Polychromatic418967fa.accept_17_12_8_4_1_2518 29 144 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 144 191 (accept_3_2 28 144 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 144 191 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 144 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 144 191
  (Polychromatic418967fa.accept_7_5_4_2_1_235 26 144 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 144 191 (accept_3_2 25 144 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 144 191 (Polychromatic418967fa.accept_13_11_1_9_1_1179 24 144 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 144 191 (Polychromatic418967fa.accept_13_10_1_9_1_3380 23 144 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 144 191 (accept_3_2 22 144 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 144 191 (Polychromatic418967fa.accept_13_8_1_9_1_1178 21 144
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 144 191
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 144 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 144 191 (accept_3_2 19 144 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 144 191 (Polychromatic418967fa.accept_13_5_1_9_1_618 18 144 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 144 191 (Polychromatic418967fa.accept_10_7_4_1_1_1319 17 144 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 144 191 (accept_3_2 16 144 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 144 191 (Polychromatic418967fa.accept_10_5_4_1_1_842 15 144
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 144 191
  (Polychromatic418967fa.accept_22_14_12_15_1_11098 14 144 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 144 191 (accept_3_2 13 144 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 144 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 144 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 144 191 (Polychromatic418967fa.accept_13_11_1_9_1_1179 11 144
  191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 144 191 (accept_3_2 10 144
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 144 191
  (Polychromatic418967fa.accept_19_9_11_1_1_8239 9 144 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 144 191 (Polychromatic418967fa.accept_11_8_1_4_1_2318 8 144 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 144 191 (accept_3_2 7 144 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 144 191 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 144 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 144 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 5
  144 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 144 191 (accept_3_2 4 144
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 144 191
  (Polychromatic418967fa.accept_19_3_11_1_1_8319 3 144 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 144 191 (Polychromatic418967fa.accept_13_2_1_9_1_1174 2 144 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 144 191 (accept_3_2 1 144 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 144 191)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 143 191 (Eq.refl
  Bool.true) (allA_succ_of_accept 48 143 191 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 143 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 143 191 (Polychromatic418967fa.accept_7_5_3_2_1_249
  47 143 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 143 191 (accept_3_2 46
  143 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 143 191
  (Polychromatic418967fa.accept_19_7_10_1_1_5382 45 143 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 143 191 (Polychromatic418967fa.accept_19_6_10_1_1_5394 44 143 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 143 191 (accept_3_2 43 143 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 143 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 143 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 143 191 (Polychromatic418967fa.accept_7_6_3_2_1_461
  41 143 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 143 191 (accept_3_2 40
  143 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 143 191
  (Polychromatic418967fa.accept_9_3_8_2_1_162 39 143 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 143 191 (Polychromatic418967fa.accept_10_8_3_1_1_1316 38 143 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 143 191 (accept_3_2 37 143 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 143 191 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 143 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 143 191
  (Polychromatic418967fa.accept_15_5_8_11_1_2350 35 143 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 143 191 (accept_3_2 34 143 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 143 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 143 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 143 191 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 143 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 143 191 (accept_3_2 31 143 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 143 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 143 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 143 191
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 143 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 143 191 (accept_3_2 28 143 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 143 191 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 143 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 143 191 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 143 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 143 191 (accept_3_2 25 143 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 143 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 143 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 143 191
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 143 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 143 191 (accept_3_2 22 143 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 143 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 143 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 143 191 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 143 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 143 191 (accept_3_2 19 143 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 143 191 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 143 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 143 191
  (Polychromatic418967fa.accept_19_17_10_1_1_6795 17 143 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 143 191 (accept_3_2 16 143 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 143 191 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 143 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 143 191 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 143 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 143 191 (accept_3_2 13 143 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 143 191 (Polychromatic418967fa.accept_7_5_3_2_1_249
  12 143 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 143 191
  (Polychromatic418967fa.accept_19_11_10_1_1_2773 11 143 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 143 191 (accept_3_2 10 143 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 143 191 (Polychromatic418967fa.accept_19_9_10_1_1_8329 9 143 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 143 191 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 143 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 143 191 (accept_3_2 7 143 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 143 191 (Polychromatic418967fa.accept_7_6_3_2_1_461 6
  143 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 143 191
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 143 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 143 191 (accept_3_2 4 143 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  143 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 143 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 143 191 (Polychromatic418967fa.accept_10_2_3_1_1_481 2 143 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 143 191 (accept_3_2 1 143 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 143 191))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 142 191
  (Eq.refl Bool.true) (allA_of_3_0 50 142 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 141 191 (Eq.refl
  Bool.true) (allA_succ_of_accept 50 141 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 141 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 141 191 (accept_3_2 49 141 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 141 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 141 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 141 191
  (Polychromatic418967fa.accept_13_8_11_9_1_593 47 141 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 141 191 (accept_3_2 46 141 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 141 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 141 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 141 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 141 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 141 191 (accept_3_2 43 141 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 141 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 141 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 141 191
  (Polychromatic418967fa.accept_7_6_1_2_1_230 41 141 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 141 191 (accept_3_2 40 141 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 141 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 141 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 141 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 141 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 141 191 (accept_3_2 37 141 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 141 191 (Polychromatic418967fa.accept_14_8_1_9_1_2085 36 141 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 141 191
  (Polychromatic418967fa.accept_9_8_6_2_1_744 35 141 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 141 191 (accept_3_2 34 141 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 141 191 (Polychromatic418967fa.accept_13_7_11_9_1_1858 33 141 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 141 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 141 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 141 191 (accept_3_2 31 141 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 141 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 141 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 141 191
  (Polychromatic418967fa.accept_21_8_15_2_1_4805 29 141 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 141 191 (accept_3_2 28 141 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 141 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 141 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 141 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 141 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 191 (accept_3_2 25 141 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 141 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 141 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 141 191
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 141 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 141 191 (accept_3_2 22 141 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 141 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 141 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 141 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 141 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 141 191 (accept_3_2 19 141 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 141 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 141 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 141 191
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 141 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 141 191 (accept_3_2 16 141 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 141 191 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 141 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 141 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 141 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 191 (accept_3_2 13 141 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 141 191 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 141 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 141 191
  (Polychromatic418967fa.accept_19_11_8_1_1_801 11 141 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 141 191 (accept_3_2 10 141 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  141 191 (Polychromatic418967fa.accept_15_9_6_11_1_1586 9 141 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 141 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 141 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 191 (accept_3_2 7 141 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 141 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 141 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 141 191
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 141 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 141 191 (accept_3_2 4 141 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  141 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 141 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 141 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 141 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 191 (accept_3_2 1 141 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 141 191))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 140 191
  (Eq.refl Bool.true) (allA_succ_of_accept 51 140 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 140 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 140 191
  (Polychromatic418967fa.accept_12_2_8_11_1_31 50 140 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 140 191 (accept_3_2 49 140 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 140 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 140 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 140 191 (Polychromatic418967fa.accept_15_2_5_11_1_1563 47 140 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 140 191 (accept_3_2 46 140 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 140 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 140 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 140 191
  (Polychromatic418967fa.accept_9_8_5_2_1_422 44 140 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 140 191 (accept_3_2 43 140 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 140 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 140 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 140 191 (Polychromatic418967fa.accept_18_5_14_11_1_2073 41 140 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 140 191 (accept_3_2 40 140 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 140 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 140 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 140 191
  (Polychromatic418967fa.accept_12_2_8_11_1_31 38 140 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 140 191 (accept_3_2 37 140 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 140 191 (Polychromatic418967fa.accept_15_6_5_11_1_2378 36 140 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 140 191 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 140 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 140 191 (accept_3_2 34 140 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 140 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 140 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 140 191
  (Polychromatic418967fa.accept_13_6_10_9_1_4329 32 140 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 140 191 (accept_3_2 31 140 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 140 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 140 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 140 191 (Polychromatic418967fa.accept_11_7_8_4_1_718 29 140 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 140 191 (accept_3_2 28 140 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 140 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 140 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 140 191
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 140 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 140 191 (accept_3_2 25 140 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 140 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 140 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 140 191 (Polychromatic418967fa.accept_11_1_8_4_1_717 23 140 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 140 191 (accept_3_2 22 140 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 140 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 140 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 140 191
  (Polychromatic418967fa.accept_16_4_12_15_1_6289 20 140 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 140 191 (accept_3_2 19 140 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 140 191 (Polychromatic418967fa.accept_11_7_8_4_1_718 18 140 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 140 191 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 140 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 140 191 (accept_3_2 16 140 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 140 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 15
  140 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 140 191
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 140 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 140 191 (accept_3_2 13 140 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 140 191 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 140 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 140 191 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 140 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 140 191 (accept_3_2 10 140 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 140 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 140 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 140 191
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 140 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 140 191 (accept_3_2 7 140 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  140 191 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 140 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 140 191 (Polychromatic418967fa.accept_18_5_14_11_1_2073 5 140 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 140 191 (accept_3_2 4 140 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 140 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 140 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 140 191
  (Polychromatic418967fa.accept_12_2_8_11_1_31 2 140 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 140 191 (accept_3_2 1 140 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140
  191)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 139 191 (Eq.refl Bool.true) (allA_of_3_0 53 139
  191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 54 138 191 (Eq.refl Bool.true) (allA_succ_of_accept 53 138
  191 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 138 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 138 191 (accept_3_2 52 138 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 138 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 138 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 138 191 (Polychromatic418967fa.accept_9_5_3_2_1_171 50 138 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 138 191 (accept_3_2 49 138 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 138 191 (Polychromatic418967fa.accept_20_8_18_11_1_5133 48 138 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 138 191
  (Polychromatic418967fa.accept_19_9_5_1_1_2766 47 138 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 138 191 (accept_3_2 46 138 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 138 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 138 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 138 191 (Polychromatic418967fa.accept_9_8_3_2_1_417 44 138 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 138 191 (accept_3_2 43 138 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 138 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 138 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 138 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 138 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 138 191 (accept_3_2 40 138 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 138 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 138 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 138 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 138 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 138 191 (accept_3_2 37 138 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 138 191 (Polychromatic418967fa.accept_15_6_3_11_1_848 36 138 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 138 191
  (Polychromatic418967fa.accept_9_8_3_2_1_417 35 138 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 138 191 (accept_3_2 34 138 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 138 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 138 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 138 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 138 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 138 191 (accept_3_2 31 138 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 138 191 (Polychromatic418967fa.accept_13_4_8_9_1_1156 30 138 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 138 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 138 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 138 191 (accept_3_2 28 138 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 138 191 (Polychromatic418967fa.accept_13_1_8_9_1_1154 27 138 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 138 191 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 138 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 138 191 (accept_3_2 25 138 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 138 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 138 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 138 191
  (Polychromatic418967fa.accept_9_5_3_2_1_171 23 138 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 138 191 (accept_3_2 22 138 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 138 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 138 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 138 191 (Polychromatic418967fa.accept_13_7_8_9_1_1158 20 138 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 138 191 (accept_3_2 19 138 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 138 191 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 138 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 138 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 138 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 138 191 (accept_3_2 16 138 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 138 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 138 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 138 191 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 138 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 138 191 (accept_3_2 13 138 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 138 191 (Polychromatic418967fa.accept_13_12_8_9_1_1833 12 138 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 138 191
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 138 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 138 191 (accept_3_2 10 138 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  138 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 138 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 138 191 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 138 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 138 191 (accept_3_2 7 138 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 138 191 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 138 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 138 191
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 138 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 138 191 (accept_3_2 4 138 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  138 191 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 138 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 138 191 (Polychromatic418967fa.accept_11_2_6_4_1_3028 2 138 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 138 191 (accept_3_2 1 138 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 138 191)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 137 191
  (Eq.refl Bool.true) (allA_succ_of_accept 54 137 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 137 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 137 191
  (Polychromatic418967fa.accept_19_15_4_1_1_4060 53 137 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 137 191 (accept_3_2 52 137 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 137 191 (Polychromatic418967fa.accept_15_6_2_11_1_325 51 137 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 137 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 137 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 137 191 (accept_3_2 49 137 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 137 191 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 137 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 137 191
  (Polychromatic418967fa.accept_7_5_4_2_1_235 47 137 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 137 191 (accept_3_2 46 137 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 137 191 (Polychromatic418967fa.accept_13_6_7_9_1_1848 45 137 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 137 191 (Polychromatic418967fa.accept_10_4_7_1_1_471 44 137 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 137 191 (accept_3_2 43 137 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 137 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 137 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 137 191
  (Polychromatic418967fa.accept_7_6_4_2_1_236 41 137 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 137 191 (accept_3_2 40 137 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 137 191 (Polychromatic418967fa.accept_15_9_2_11_1_2391 39 137 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 137 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 137 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 137 191 (accept_3_2 37 137 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 137 191 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 137 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 137 191
  (Polychromatic418967fa.accept_15_5_2_11_1_1596 35 137 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 137 191 (accept_3_2 34 137 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 137 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 137 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 137 191 (Polychromatic418967fa.accept_11_10_5_4_1_711 32 137 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 137 191 (accept_3_2 31 137 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 137 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 137 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 137 191
  (Polychromatic418967fa.accept_13_3_7_9_1_1153 29 137 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 137 191 (accept_3_2 28 137 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 137 191 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 137 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 137 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 137 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 137 191 (accept_3_2 25 137 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 137 191 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 137 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 137 191
  (Polychromatic418967fa.accept_22_1_5_15_1_3074 23 137 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 137 191 (accept_3_2 22 137 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 137 191 (Polychromatic418967fa.accept_11_10_5_4_1_711 21 137 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 137 191 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 137 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 137 191 (accept_3_2 19 137 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 137 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 137 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 137 191
  (Polychromatic418967fa.accept_13_4_7_9_1_5260 17 137 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 137 191 (accept_3_2 16 137 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 137 191 (Polychromatic418967fa.accept_13_2_7_9_1_2616 15 137 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 137 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 137 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 137 191 (accept_3_2 13 137 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 137 191 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 137 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 137 191
  (Polychromatic418967fa.accept_13_11_7_9_1_612 11 137 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 137 191 (accept_3_2 10 137 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  137 191 (Polychromatic418967fa.accept_15_9_2_11_1_2391 9 137 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 137 191 (Polychromatic418967fa.accept_13_8_7_9_1_611 8 137 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 137 191 (accept_3_2 7 137 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 137 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 137 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 137 191
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 137 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 137 191 (accept_3_2 4 137 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  137 191 (Polychromatic418967fa.accept_13_3_7_9_1_1153 3 137 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 137 191 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 137 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 137 191 (accept_3_2 1 137 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 137 191))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 136 191
  (Eq.refl Bool.true) (allA_of_3_0 56 136 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 57 135 191 (Eq.refl
  Bool.true) (allA_succ_of_accept 56 135 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 135 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 135 191 (accept_3_2 55 135 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 135 191 (Polychromatic418967fa.accept_10_4_5_1_1_497 54 135 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 135 191
  (Polychromatic418967fa.accept_13_1_5_9_1_226 53 135 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 135 191 (accept_3_2 52 135 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 135 191 (Polychromatic418967fa.accept_11_7_3_4_1_729 51 135 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 135 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 135 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 135 191 (accept_3_2 49 135 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 135 191 (Polychromatic418967fa.accept_18_12_9_11_1_4370 48 135 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 135 191
  (Polychromatic418967fa.accept_19_9_2_1_1_2821 47 135 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 135 191 (accept_3_2 46 135 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 135 191 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 135 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 135 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 135 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 135 191 (accept_3_2 43 135 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 135 191 (Polychromatic418967fa.accept_13_3_5_9_1_5285 42 135 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 135 191
  (Polychromatic418967fa.accept_13_2_5_9_1_610 41 135 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 135 191 (accept_3_2 40 135 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 135 191 (Polychromatic418967fa.accept_10_9_5_1_1_1325 39 135 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 135 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 135 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 135 191 (accept_3_2 37 135 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 135 191 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 135 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 135 191
  (Polychromatic418967fa.accept_16_3_7_15_1_1130 35 135 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 135 191 (accept_3_2 34 135 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 135 191 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 135 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 135 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 135 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 135 191 (accept_3_2 31 135 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 135 191 (Polychromatic418967fa.accept_13_4_5_9_1_1829 30 135 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 135 191
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 135 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 135 191 (accept_3_2 28 135 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 135 191 (Polychromatic418967fa.accept_13_1_5_9_1_226 27 135 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 135 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 135 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 135 191 (accept_3_2 25 135 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 135 191 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 135 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 135 191
  (Polychromatic418967fa.accept_22_1_3_15_1_11046 23 135 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 135 191 (accept_3_2 22 135 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 135 191 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 135 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 135 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 135 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 135 191 (accept_3_2 19 135 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 135 191 (Polychromatic418967fa.accept_11_7_3_4_1_729
  18 135 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 135 191
  (Polychromatic418967fa.accept_13_4_5_9_1_1829 17 135 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 135 191 (accept_3_2 16 135 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 135 191 (Polychromatic418967fa.accept_13_2_5_9_1_610 15 135 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 135 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 135 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 191 (accept_3_2 13 135 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 135 191 (Polychromatic418967fa.accept_18_12_9_11_1_4370 12 135 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 135 191
  (Polychromatic418967fa.accept_16_11_7_15_1_1998 11 135 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 135 191 (accept_3_2 10 135 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 135 191 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 135 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 135 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 135 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 191 (accept_3_2 7 135 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 135 191 (Polychromatic418967fa.accept_10_6_5_1_1_482 6
  135 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 135 191
  (Polychromatic418967fa.accept_17_5_16_4_1_4734 5 135 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 135 191 (accept_3_2 4 135 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  135 191 (Polychromatic418967fa.accept_13_3_5_9_1_5285 3 135 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 135 191 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 135 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 191 (accept_3_2 1 135 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 135 191))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 134 191
  (Eq.refl Bool.true) (allA_succ_of_accept 57 134 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 134 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 134 191
  (Polychromatic418967fa.accept_12_8_2_11_1_246 56 134 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 134 191 (accept_3_2 55 134 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 134 191 (Polychromatic418967fa.accept_23_8_19_7_1_11097 54 134 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 134 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 134 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 134 191 (accept_3_2 52 134 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 134 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 134 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 134 191
  (Polychromatic418967fa.accept_9_5_8_2_1_409 50 134 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 134 191 (accept_3_2 49 134 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 134 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 134 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 134 191 (Polychromatic418967fa.accept_10_7_4_1_1_1319 47 134 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 134 191 (accept_3_2 46 134 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 134 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 134 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 134 191
  (Polychromatic418967fa.accept_12_8_2_11_1_246 44 134 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 134 191 (accept_3_2 43 134 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 134 191 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 134 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 134 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 134 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 134 191 (accept_3_2 40 134 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 134 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 134 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 134 191
  (Polychromatic418967fa.accept_7_3_1_2_1_247 38 134 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 134 191 (accept_3_2 37 134 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 134 191 (Polychromatic418967fa.accept_17_2_15_4_1_4723 36 134 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 134 191 (Polychromatic418967fa.accept_10_5_4_1_1_842 35 134 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 134 191 (accept_3_2 34 134 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 134 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 134 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 134 191
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 134 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 134 191 (accept_3_2 31 134 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 134 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 134 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 134 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 134 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 134 191 (accept_3_2 28 134 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 134 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 134 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 134 191
  (Polychromatic418967fa.accept_20_6_14_11_1_6537 26 134 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 134 191 (accept_3_2 25 134 191 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 134 191 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 134 191 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 134 191 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 134 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 134 191 (accept_3_2 22 134 191
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 134 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 21
  134 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 134 191
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 134 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 134 191 (accept_3_2 19 134 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 134 191 (Polychromatic418967fa.accept_13_5_4_9_1_601 18 134 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 134 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 134 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 134 191 (accept_3_2 16 134 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 134 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 134 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 134 191
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 134 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 134 191 (accept_3_2 13 134 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 134 191 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 134 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 134 191 (Polychromatic418967fa.accept_17_11_15_4_1_2415 11 134 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 134 191 (accept_3_2 10 134 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 134 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 134 191
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 134 191
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 134 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 134 191 (accept_3_2 7 134 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  134 191 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 134 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 134 191 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 134 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 134 191 (accept_3_2 4 134 191 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 134 191 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 134 191 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 134 191
  (Polychromatic418967fa.accept_17_2_15_4_1_4723 2 134 191 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 134 191 (accept_3_2 1 134 191 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134
  191))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_191_segment_000)))))))))))))))))))))))))))))))))))))))))))))))))))))))))


