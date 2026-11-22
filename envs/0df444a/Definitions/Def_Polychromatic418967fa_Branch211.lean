-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch211
-- name    : Polychromatic418967fa_Branch211
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:23:09.83312+00:00
-- url     : https://prove2.me/theorems/7f7f0aca-6785-4d5a-8b83-75653d024673
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch211_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_211 : allB 211 211 :=
  allB_succ' 2 210 211 (Eq.refl Bool.true) (allA_succ_of_accept 1 210 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 1
  210 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 210 211)) (allB_succ' 3 209 211
  (Eq.refl Bool.true) (allA_of_3_1 3 209 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 208 211 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 208 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 208 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 208 211 (accept_3_3 2 208 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 208 211 (Polychromatic418967fa.accept_11_1_10_2_1_58 1 208 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 208 211)))) (allB_succ' 5 207 211 (Eq.refl Bool.true)
  (allA_succ_of_accept 4 207 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 207 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 207 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 207 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 207 211 (accept_3_3 2 207 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 207 211 (Polychromatic418967fa.accept_20_1_7_11_1_3673
  1 207 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 207 211))))) (allB_succ' 6 206 211
  (Eq.refl Bool.true) (allA_of_3_1 6 206 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 205 211 (Eq.refl
  Bool.true) (allA_succ_of_accept 6 205 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 205 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 205 211 (accept_3_3 5 205 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 205 211 (Polychromatic418967fa.accept_10_4_5_1_1_497 4 205 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 205 211
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 205 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 205 211 (accept_3_3 2 205 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  205 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 205 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 205 211))))))) (allB_succ' 8 204 211 (Eq.refl Bool.true) (allA_succ_of_accept 7 204 211
  (Polychromatic418967fa.accept_8_7_4_3_1_156 7 204 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 204 211 (Polychromatic418967fa.accept_13_6_9_3_1_915 6 204 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 204 211 (accept_3_3 5 204 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 204 211 (Polychromatic418967fa.accept_11_4_6_2_1_51 4 204 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 204 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 3
  204 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 204 211 (accept_3_3 2 204
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 204 211 (Polychromatic418967fa.accept_9_1_6_4_1_49
  1 204 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 204 211)))))))) (allB_succ' 9 203 211
  (Eq.refl Bool.true) (allA_of_3_1 9 203 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 202 211 (Eq.refl
  Bool.true) (allA_succ_of_accept 9 202 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 202 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 202 211 (accept_3_3 8 202 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 202 211 (Polychromatic418967fa.accept_14_7_6_1_1_1656 7 202 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 202 211
  (Polychromatic418967fa.accept_10_6_2_1_1_494 6 202 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 202 211 (accept_3_3 5 202 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  202 211 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 202 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 202 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 202 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 202 211 (accept_3_3 2 202 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 202 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 202 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 202 211)))))))))) (allB_succ' 11 201 211 (Eq.refl
  Bool.true) (allA_succ_of_accept 10 201 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 201 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 201 211 (Polychromatic418967fa.accept_13_9_6_3_1_1514
  9 201 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 201 211 (accept_3_3 8
  201 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 201 211
  (Polychromatic418967fa.accept_9_7_3_4_1_218 7 201 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 201 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 201 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 201 211 (accept_3_3 5 201 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 201 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 201 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 201 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 3
  201 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 201 211 (accept_3_3 2 201
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 201 211 (Polychromatic418967fa.accept_9_1_3_4_1_47
  1 201 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 201 211))))))))))) (allB_succ' 12 200
  211 (Eq.refl Bool.true) (allA_of_3_1 12 200 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 199 211
  (Eq.refl Bool.true) (allA_succ_of_accept 12 199 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 199 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 199 211 (accept_3_3 11 199 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 199 211 (Polychromatic418967fa.accept_11_10_1_2_1_1624 10 199
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 199 211
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 199 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 199 211 (accept_3_3 8 199 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  199 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 199 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 199 211 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 199 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 199 211 (accept_3_3 5 199 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 199 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 199 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 199 211
  (Polychromatic418967fa.accept_9_3_1_4_1_216 3 199 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 199 211 (accept_3_3 2 199 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  199 211 (Polychromatic418967fa.accept_13_1_4_3_1_1545 1 199 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 199 211))))))))))))) (allB_succ' 14 198 211 (Eq.refl Bool.true) (allA_succ_of_accept 13 198 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 198 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 198 211 (Polychromatic418967fa.accept_21_12_9_1_1_9528 12 198 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 198 211 (accept_3_3 11 198 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 198 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 198 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 198 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 9
  198 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 198 211 (accept_3_3 8 198
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 198 211
  (Polychromatic418967fa.accept_20_7_18_11_1_5080 7 198 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 198 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 198 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 198 211 (accept_3_3 5 198 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 198 211 (Polychromatic418967fa.accept_15_4_3_1_1_487 4 198 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 198 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 3
  198 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 198 211 (accept_3_3 2 198
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 198 211 (Polychromatic418967fa.accept_4_1_2_3_1_9
  1 198 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 198 211)))))))))))))) (allB_succ' 15
  197 211 (Eq.refl Bool.true) (allA_of_3_1 15 197 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 196 211
  (Eq.refl Bool.true) (allA_succ_of_accept 15 196 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 196 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 196 211 (accept_3_3 14 196 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 196 211 (Polychromatic418967fa.accept_19_13_6_2_1_4124 13 196
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 196 211
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 196 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 196 211 (accept_3_3 11 196 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 196 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 196 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 196 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 196 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 196 211 (accept_3_3 8 196 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 196 211 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 196 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 196 211
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 196 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 196 211 (accept_3_3 5 196 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  196 211 (Polychromatic418967fa.accept_11_4_9_2_1_259 4 196 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 196 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 196 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 196 211 (accept_3_3 2 196 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 196 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 196 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 196 211)))))))))))))))) (allB_succ' 17 195 211 (Eq.refl
  Bool.true) (allA_succ_of_accept 16 195 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 195 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 195 211
  (Polychromatic418967fa.accept_21_15_6_1_1_6306 15 195 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 195 211 (accept_3_3 14 195 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 195 211 (Polychromatic418967fa.accept_20_13_15_11_1_6610 13 195 211 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 195 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 195 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 195 211 (accept_3_3 11 195 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 195 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 195 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 195 211
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 195 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 195 211 (accept_3_3 8 195 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  195 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 195 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 195 211 (Polychromatic418967fa.accept_10_6_5_1_1_482 6 195 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 195 211 (accept_3_3 5 195 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 195 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 195 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 195 211
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 195 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 195 211 (accept_3_3 2 195 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  195 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 195 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 195 211))))))))))))))))) (allB_succ' 18 194 211 (Eq.refl Bool.true) (allA_of_3_1 18 194 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 193 211 (Eq.refl Bool.true) (allA_succ_of_accept 18 193 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 193 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 193 211 (accept_3_3 17 193 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 193 211 (Polychromatic418967fa.accept_17_16_6_7_1_2715 16 193 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 193 211 (Polychromatic418967fa.accept_11_4_6_2_1_51 15 193 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 193 211 (accept_3_3 14 193 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 193 211 (Polychromatic418967fa.accept_16_13_1_3_1_2205 13 193 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 193 211
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 193 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 193 211 (accept_3_3 11 193 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 193 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 193 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 193 211 (Polychromatic418967fa.accept_24_9_1_19_1_941 9 193 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 193 211 (accept_3_3 8 193 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 193 211 (Polychromatic418967fa.accept_13_7_11_3_1_1540 7 193 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 193 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 193 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 193 211 (accept_3_3 5 193 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  193 211 (Polychromatic418967fa.accept_11_4_6_2_1_51 4 193 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 193 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 193 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 193 211 (accept_3_3 2 193 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 193 211 (Polychromatic418967fa.accept_13_1_11_3_1_901 1 193 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 193 211))))))))))))))))))) (allB_succ' 20 192 211
  (Eq.refl Bool.true) (allA_succ_of_accept 19 192 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 192 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 192 211
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 192 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 192 211 (accept_3_3 17 192 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 192 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 192 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 192 211 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 192 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 192 211 (accept_3_3 14 192 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 192 211 (Polychromatic418967fa.accept_10_3_2_1_1_839 13 192 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 192 211
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 192 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 192 211 (accept_3_3 11 192 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 192 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 192 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 192 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 192 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 192 211 (accept_3_3 8 192 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 192 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 192 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 192 211
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 192 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 192 211 (accept_3_3 5 192 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  192 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 192 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 192 211 (Polychromatic418967fa.accept_10_3_2_1_1_839 3 192 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 192 211 (accept_3_3 2 192 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 192 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 192 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 192 211)))))))))))))))))))) (allB_succ' 21 191 211
  (Eq.refl Bool.true) (allA_of_3_1 21 191 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 190 211 (Eq.refl
  Bool.true) (allA_succ_of_accept 21 190 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 190 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 190 211 (accept_3_3 20 190 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 190 211 (Polychromatic418967fa.accept_18_1_10_13_1_500 19 190 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 190 211
  (Polychromatic418967fa.accept_13_5_8_3_1_1535 18 190 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 190 211 (accept_3_3 17 190 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 190 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 190 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 190 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 190 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 190 211 (accept_3_3 14 190 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 190 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 190 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 190 211
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 190 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 190 211 (accept_3_3 11 190 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 190 211 (Polychromatic418967fa.accept_17_10_3_7_1_1679 10 190 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 190 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 190 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 190 211 (accept_3_3 8 190 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 190 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 190 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 190 211
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 190 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 190 211 (accept_3_3 5 190 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  190 211 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 190 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 190 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 190 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 190 211 (accept_3_3 2 190 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 190 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 190 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 190 211)))))))))))))))))))))) (allB_succ' 23 189 211
  (Eq.refl Bool.true) (allA_succ_of_accept 22 189 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 189 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 189 211
  (Polychromatic418967fa.accept_13_8_7_3_1_430 21 189 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 189 211 (accept_3_3 20 189 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 189 211 (Polychromatic418967fa.accept_23_19_5_4_1_12535 19 189 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 189 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 189 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 189 211 (accept_3_3 17 189 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 189 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 189 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 189 211
  (Polychromatic418967fa.accept_10_5_9_1_1_187 15 189 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 189 211 (accept_3_3 14 189 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 189 211 (Polychromatic418967fa.accept_14_13_7_1_1_1618 13 189 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 189 211 (Polychromatic418967fa.accept_10_2_9_1_1_185 12 189 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 189 211 (accept_3_3 11 189 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 189 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 189 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 189 211
  (Polychromatic418967fa.accept_13_9_7_3_1_1531 9 189 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 189 211 (accept_3_3 8 189 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  189 211 (Polychromatic418967fa.accept_15_7_9_1_1_473 7 189 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 189 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 189 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 189 211 (accept_3_3 5 189 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 189 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 189 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 189 211
  (Polychromatic418967fa.accept_12_3_9_7_1_472 3 189 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 189 211 (accept_3_3 2 189 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  189 211 (Polychromatic418967fa.accept_13_1_7_3_1_1503 1 189 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 189 211))))))))))))))))))))))) (allB_succ' 24 188 211 (Eq.refl Bool.true) (allA_of_3_1 24 188
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 187 211 (Eq.refl Bool.true) (allA_succ_of_accept 24 187
  211 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 187 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 187 211 (accept_3_3 23 187 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 187 211 (Polychromatic418967fa.accept_13_9_5_3_1_428 22 187 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 187 211 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 187 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 187 211 (accept_3_3 20 187 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 187 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 187 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 187 211
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 187 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 187 211 (accept_3_3 17 187 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 187 211 (Polychromatic418967fa.accept_10_6_7_1_1_1297 16 187 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 187 211 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 187 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 187 211 (accept_3_3 14 187 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 187 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 187 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 187 211
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 187 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 187 211 (accept_3_3 11 187 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 187 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 187 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 187 211 (Polychromatic418967fa.accept_13_9_5_3_1_428 9 187 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 187 211 (accept_3_3 8 187 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 187 211 (Polychromatic418967fa.accept_16_7_11_3_1_1330 7 187 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 187 211
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 187 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 187 211 (accept_3_3 5 187 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  187 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 187 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 187 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 187 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 187 211 (accept_3_3 2 187 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 187 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 187 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 187 211))))))))))))))))))))))))) (allB_succ' 26 186 211
  (Eq.refl Bool.true) (allA_succ_of_accept 25 186 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 186 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 186 211
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 186 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 186 211 (accept_3_3 23 186 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 186 211 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 186 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 186 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 186 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 186 211 (accept_3_3 20 186 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 186 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 186 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 186 211
  (Polychromatic418967fa.accept_15_3_6_1_1_1834 18 186 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 186 211 (accept_3_3 17 186 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 186 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 186 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 186 211 (Polychromatic418967fa.accept_10_5_6_1_1_836 15 186 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 186 211 (accept_3_3 14 186 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 186 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 186 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 186 211
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 186 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 186 211 (accept_3_3 11 186 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 186 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 186 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 186 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 186 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 186 211 (accept_3_3 8 186 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 186 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 186 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 186 211
  (Polychromatic418967fa.accept_17_6_16_7_1_12533 6 186 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 186 211 (accept_3_3 5 186 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  186 211 (Polychromatic418967fa.accept_21_4_18_1_1_6333 4 186 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 186 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 186 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 186 211 (accept_3_3 2 186 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 186 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 186 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186 211)))))))))))))))))))))))))) (allB_succ' 27 185 211
  (Eq.refl Bool.true) (allA_of_3_1 27 185 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 184 211 (Eq.refl
  Bool.true) (allA_succ_of_accept 27 184 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 184 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 184 211 (accept_3_3 26 184 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 184 211 (Polychromatic418967fa.accept_10_5_4_1_1_842 25 184 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 184 211
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 184 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 184 211 (accept_3_3 23 184 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 184 211 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 184 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 184 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 184 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 184 211 (accept_3_3 20 184 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 184 211 (Polychromatic418967fa.accept_21_19_16_1_1_2053 19 184 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 184 211
  (Polychromatic418967fa.accept_13_5_2_3_1_1526 18 184 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 184 211 (accept_3_3 17 184 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 184 211 (Polychromatic418967fa.accept_11_5_8_2_1_588 16 184 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 184 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 184 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 184 211 (accept_3_3 14 184 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 184 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 184 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 184 211
  (Polychromatic418967fa.accept_13_12_2_3_1_1527 12 184 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 184 211 (accept_3_3 11 184 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 184 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 184 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 184 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 184 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 184 211 (accept_3_3 8 184 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 184 211 (Polychromatic418967fa.accept_10_7_4_1_1_1319 7 184 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 184 211
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 184 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 184 211 (accept_3_3 5 184 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  184 211 (Polychromatic418967fa.accept_16_4_8_3_1_4206 4 184 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 184 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 184 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 184 211 (accept_3_3 2 184 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 184 211 (Polychromatic418967fa.accept_13_1_2_3_1_911 1 184 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 184 211)))))))))))))))))))))))))))) (allB_succ' 29 183
  211 (Eq.refl Bool.true) (allA_succ_of_accept 28 183 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 183 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 183 211
  (Polychromatic418967fa.accept_16_11_7_3_1_3163 27 183 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 183 211 (accept_3_3 26 183 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 183 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 183 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 183 211 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 183 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 183 211 (accept_3_3 23 183 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 183 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 183 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 183 211
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 183 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 183 211 (accept_3_3 20 183 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 183 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 183 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 183 211 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 183 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 183 211 (accept_3_3 17 183 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 183 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 183 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 183 211
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 183 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 183 211 (accept_3_3 14 183 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 183 211 (Polychromatic418967fa.accept_15_13_3_1_1_3740 13 183 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 183 211 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 183 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 183 211 (accept_3_3 11 183 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 183 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 183 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 183 211
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 183 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 183 211 (accept_3_3 8 183 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  183 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 183 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 183 211 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 183 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 183 211 (accept_3_3 5 183 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 183 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 183 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 183 211
  (Polychromatic418967fa.accept_19_3_12_2_1_9788 3 183 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 183 211 (accept_3_3 2 183 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  183 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 183 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 183 211))))))))))))))))))))))))))))) (allB_succ' 30 182 211 (Eq.refl Bool.true) (allA_of_3_1 30
  182 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 181 211 (Eq.refl Bool.true) (allA_succ_of_accept 30
  181 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 181 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 181 211 (accept_3_3 29 181 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 181 211 (Polychromatic418967fa.accept_13_2_12_3_1_415 28 181 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 181 211 (Polychromatic418967fa.accept_19_8_10_2_1_5414 27 181
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 181 211 (accept_3_3 26 181
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 181 211
  (Polychromatic418967fa.accept_9_7_1_4_1_217 25 181 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 181 211 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 181 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 181 211 (accept_3_3 23 181 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 181 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 181 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 181 211 (Polychromatic418967fa.accept_9_3_1_4_1_216
  21 181 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 181 211 (accept_3_3 20
  181 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 181 211
  (Polychromatic418967fa.accept_7_5_6_1_1_407 19 181 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 181 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 181 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 181 211 (accept_3_3 17 181 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 181 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 181 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 181 211 (Polychromatic418967fa.accept_9_6_1_4_1_474
  15 181 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 181 211 (accept_3_3 14
  181 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 181 211
  (Polychromatic418967fa.accept_17_13_11_7_1_4961 13 181 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 181 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 181 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 181 211 (accept_3_3 11 181 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 181 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 181 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 181 211
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 181 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 181 211 (accept_3_3 8 181 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  181 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 181 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 181 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 181 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 181 211 (accept_3_3 5 181 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 181 211 (Polychromatic418967fa.accept_13_4_12_3_1_2999 4 181 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 181 211
  (Polychromatic418967fa.accept_9_3_1_4_1_216 3 181 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 181 211 (accept_3_3 2 181 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  181 211 (Polychromatic418967fa.accept_17_1_11_7_1_4962 1 181 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 181 211))))))))))))))))))))))))))))))) (allB_succ' 32 180 211 (Eq.refl Bool.true)
  (allA_succ_of_accept 31 180 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 180 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 180 211 (Polychromatic418967fa.accept_19_11_9_2_1_1729 30 180
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 180 211 (accept_3_3 29 180
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 180 211
  (Polychromatic418967fa.accept_11_6_4_2_1_599 28 180 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 180 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 180 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 180 211 (accept_3_3 26 180 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 180 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 180 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 180 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 24
  180 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 180 211 (accept_3_3 23
  180 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 180 211
  (Polychromatic418967fa.accept_16_6_4_3_1_2189 22 180 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 180 211 (Polychromatic418967fa.accept_13_8_11_3_1_3053 21 180 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 180 211 (accept_3_3 20 180 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 180 211 (Polychromatic418967fa.accept_21_19_12_1_1_11027 19 180 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 180 211
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 180 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 180 211 (accept_3_3 17 180 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 180 211 (Polychromatic418967fa.accept_17_16_10_7_1_2671 16 180 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 180 211 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 180 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 180 211 (accept_3_3 14 180 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 180 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 180 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 180 211
  (Polychromatic418967fa.accept_16_12_4_3_1_4295 12 180 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 180 211 (accept_3_3 11 180 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 180 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 180 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 180 211 (Polychromatic418967fa.accept_11_9_4_2_1_600 9 180 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 180 211 (accept_3_3 8 180 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 180 211 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 180 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 180 211
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 180 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 180 211 (accept_3_3 5 180 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  180 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 180 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 180 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 180 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 180 211 (accept_3_3 2 180 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 180 211 (Polychromatic418967fa.accept_13_1_11_3_1_901 1 180 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 180 211)))))))))))))))))))))))))))))))) (allB_succ' 33
  179 211 (Eq.refl Bool.true) (allA_of_3_1 33 179 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 178 211
  (Eq.refl Bool.true) (allA_succ_of_accept 33 178 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 178 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 178 211 (accept_3_3 32 178 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 178 211 (Polychromatic418967fa.accept_13_5_9_3_1_870 31 178
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 178 211
  (Polychromatic418967fa.accept_7_2_3_1_1_10 30 178 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 178 211 (accept_3_3 29 178 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 178 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 178 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 178 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 178 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 178 211 (accept_3_3 26 178 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 178 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 178 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 178 211
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 178 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 178 211 (accept_3_3 23 178 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 178 211 (Polychromatic418967fa.accept_16_6_2_3_1_4223 22 178 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 178 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 178 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 178 211 (accept_3_3 20 178 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 178 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 178 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 178 211
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 178 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 178 211 (accept_3_3 17 178 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 178 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 178 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 178 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 178 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 178 211 (accept_3_3 14 178 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 178 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 178 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 178 211
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 178 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 178 211 (accept_3_3 11 178 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 178 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 178 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 178 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 178 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 178 211 (accept_3_3 8 178 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 178 211 (Polychromatic418967fa.accept_13_7_9_3_1_1504 7 178 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 178 211
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 178 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 178 211 (accept_3_3 5 178 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  178 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 178 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 178 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 178 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 178 211 (accept_3_3 2 178 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 178 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 178 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 178 211)))))))))))))))))))))))))))))))))) (allB_succ' 35
  177 211 (Eq.refl Bool.true) (allA_succ_of_accept 34 177 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 177 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 177 211
  (Polychromatic418967fa.accept_13_7_8_3_1_1533 33 177 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 177 211 (accept_3_3 32 177 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 177 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 177 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 177 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 177 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 177 211 (accept_3_3 29 177 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 177 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 177 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 177 211
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 177 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 177 211 (accept_3_3 26 177 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 177 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 177 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 177 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 177 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 177 211 (accept_3_3 23 177 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 177 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 177 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 177 211
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 177 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 177 211 (accept_3_3 20 177 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 177 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 177 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 177 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 177 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 177 211 (accept_3_3 17 177 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 177 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 177 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 177 211
  (Polychromatic418967fa.accept_12_3_9_7_1_472 15 177 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 177 211 (accept_3_3 14 177 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 177 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 177 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 177 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 177 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 177 211 (accept_3_3 11 177 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 177 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 177 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 177 211
  (Polychromatic418967fa.accept_13_9_8_3_1_3045 9 177 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 177 211 (accept_3_3 8 177 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  177 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 177 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 177 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 177 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 177 211 (accept_3_3 5 177 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 177 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 177 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 177 211
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 177 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 177 211 (accept_3_3 2 177 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  177 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 177 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 177 211))))))))))))))))))))))))))))))))))) (allB_succ' 36 176 211 (Eq.refl Bool.true)
  (allA_of_3_1 36 176 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 175 211 (Eq.refl Bool.true)
  (allA_succ_of_accept 36 175 211 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 175 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 175 211 (accept_3_3 35 175 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 175 211 (Polychromatic418967fa.accept_10_4_5_1_1_497 34 175 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 175 211
  (Polychromatic418967fa.accept_19_14_4_2_1_2840 33 175 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 175 211 (accept_3_3 32 175 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 175 211 (Polychromatic418967fa.accept_13_5_6_3_1_868 31 175 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 175 211 (Polychromatic418967fa.accept_19_11_4_2_1_1700 30 175 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 175 211 (accept_3_3 29 175 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 175 211 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 175 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 175 211
  (Polychromatic418967fa.accept_13_1_6_3_1_1547 27 175 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 175 211 (accept_3_3 26 175 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 175 211 (Polychromatic418967fa.accept_19_6_4_2_1_1726 25 175 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 175 211 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 175 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 175 211 (accept_3_3 23 175 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 175 211 (Polychromatic418967fa.accept_13_9_6_3_1_1514 22 175
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 175 211
  (Polychromatic418967fa.accept_15_6_10_1_1_3675 21 175 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 175 211 (accept_3_3 20 175 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 175 211 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 175 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 175 211 (Polychromatic418967fa.accept_13_5_6_3_1_868 18 175 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 175 211 (accept_3_3 17 175 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 175 211 (Polychromatic418967fa.accept_10_6_5_1_1_482 16 175
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 175 211
  (Polychromatic418967fa.accept_17_15_5_7_1_2694 15 175 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 175 211 (accept_3_3 14 175 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 175 211 (Polychromatic418967fa.accept_14_13_7_1_1_1618 13 175 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 175 211 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 175 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 175 211 (accept_3_3 11 175 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 175 211 (Polychromatic418967fa.accept_13_10_6_3_1_1515 10 175 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 175 211
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 175 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 175 211 (accept_3_3 8 175 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  175 211 (Polychromatic418967fa.accept_15_7_10_1_1_1836 7 175 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 175 211 (Polychromatic418967fa.accept_10_6_5_1_1_482 6 175 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 175 211 (accept_3_3 5 175 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 175 211 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 175 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 175 211
  (Polychromatic418967fa.accept_21_3_7_1_1_9521 3 175 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 175 211 (accept_3_3 2 175 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  175 211 (Polychromatic418967fa.accept_11_1_10_2_1_58 1 175 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 175 211))))))))))))))))))))))))))))))))))))) (allB_succ' 38 174 211 (Eq.refl Bool.true)
  (allA_succ_of_accept 37 174 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 174 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 174 211 (Polychromatic418967fa.accept_15_6_9_1_1_1823 36 174
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 174 211 (accept_3_3 35 174
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 174 211
  (Polychromatic418967fa.accept_9_7_3_4_1_218 34 174 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 174 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 174 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 174 211 (accept_3_3 32 174 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 174 211 (Polychromatic418967fa.accept_17_14_4_7_1_7439 31 174 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 174 211
  (Polychromatic418967fa.accept_7_2_6_1_1_73 30 174 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 174 211 (accept_3_3 29 174 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 174 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 174 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 174 211 (Polychromatic418967fa.accept_10_7_4_1_1_1319 27 174 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 174 211 (accept_3_3 26 174 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 174 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 174 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 174 211
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 174 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 174 211 (accept_3_3 23 174 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 174 211 (Polychromatic418967fa.accept_13_9_5_3_1_428 22 174 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 174 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 174 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 174 211 (accept_3_3 20 174 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 174 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 174 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 174 211
  (Polychromatic418967fa.accept_11_7_9_2_1_260 18 174 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 174 211 (accept_3_3 17 174 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 174 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 174 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 174 211 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 174 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 174 211 (accept_3_3 14 174 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 174 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 174 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 174 211
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 174 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 174 211 (accept_3_3 11 174 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 174 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 174 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 174 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 174 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 174 211 (accept_3_3 8 174 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 174 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 174 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 174 211
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 174 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 174 211 (accept_3_3 5 174 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  174 211 (Polychromatic418967fa.accept_11_4_9_2_1_259 4 174 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 174 211 (Polychromatic418967fa.accept_17_3_4_7_1_1658 3 174 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 174 211 (accept_3_3 2 174 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 174 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 174 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174 211))))))))))))))))))))))))))))))))))))))
  (allB_succ' 39 173 211 (Eq.refl Bool.true) (allA_of_3_1 39 173 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 40 172 211 (Eq.refl Bool.true) (allA_succ_of_accept 39 172 211 (Polychromatic418967fa.accept_6_3_4_1_1_8
  39 172 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 172 211 (accept_3_3 38
  172 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 172 211
  (Polychromatic418967fa.accept_18_1_10_13_1_500 37 172 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 172 211 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 172 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 172 211 (accept_3_3 35 172 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 172 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 172 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 172 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 33
  172 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 172 211 (accept_3_3 32
  172 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 172 211
  (Polychromatic418967fa.accept_7_3_4_1_1_71 31 172 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 172 211 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 172 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 172 211 (accept_3_3 29 172 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 172 211 (Polychromatic418967fa.accept_19_9_1_2_1_6839 28 172 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 172 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 172 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 172 211 (accept_3_3 26 172 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 172 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 172 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 172 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 172 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 172 211 (accept_3_3 23 172 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 172 211 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 172 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 172 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 172 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 172 211 (accept_3_3 20 172 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 172 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 172 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 172 211 (Polychromatic418967fa.accept_19_18_1_2_1_5430 18 172 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 172 211 (accept_3_3 17 172 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 172 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 172 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 172 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 172 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 172 211 (accept_3_3 14 172 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 172 211 (Polychromatic418967fa.accept_10_3_2_1_1_839 13 172 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 172 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 172 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 172 211 (accept_3_3 11 172 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 172 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 172 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 172 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 172 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 172 211 (accept_3_3 8 172 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  172 211 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 172 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 172 211 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 172 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 172 211 (accept_3_3 5 172 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 172 211 (Polychromatic418967fa.accept_16_4_12_3_1_2180 4 172 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 172 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 172 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 172 211 (accept_3_3 2 172 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  172 211 (Polychromatic418967fa.accept_18_1_10_13_1_500 1 172 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 172 211)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 171 211 (Eq.refl Bool.true)
  (allA_succ_of_accept 40 171 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 171 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 171 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 171 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 171 211 (accept_3_3 38 171 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 171 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 37
  171 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 171 211
  (Polychromatic418967fa.accept_13_10_2_3_1_3025 36 171 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 171 211 (accept_3_3 35 171 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 171 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 171 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 171 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 171 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 171 211 (accept_3_3 32 171 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 171 211 (Polychromatic418967fa.accept_13_5_2_3_1_1526 31 171 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 171 211
  (Polychromatic418967fa.accept_7_2_3_1_1_10 30 171 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 171 211 (accept_3_3 29 171 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 171 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 171 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 171 211 (Polychromatic418967fa.accept_13_1_2_3_1_911 27 171 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 171 211 (accept_3_3 26 171 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 171 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 171 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 171 211
  (Polychromatic418967fa.accept_13_11_2_3_1_883 24 171 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 171 211 (accept_3_3 23 171 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 171 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 171 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 171 211 (Polychromatic418967fa.accept_12_9_3_7_1_924 21 171 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 171 211 (accept_3_3 20 171 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 171 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 171 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 171 211
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 171 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 171 211 (accept_3_3 17 171 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 171 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 171 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 171 211 (Polychromatic418967fa.accept_11_4_6_2_1_51 15 171 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 171 211 (accept_3_3 14 171 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 171 211 (Polychromatic418967fa.accept_23_13_10_4_1_12534 13 171 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 171 211
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 171 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 171 211 (accept_3_3 11 171 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 171 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 171 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 171 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 171 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 171 211 (accept_3_3 8 171 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 211 (Polychromatic418967fa.accept_15_7_6_1_1_1091 7 171 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 171 211
  (Polychromatic418967fa.accept_16_6_11_3_1_2198 6 171 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 171 211 (accept_3_3 5 171 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  171 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 171 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 171 211 (Polychromatic418967fa.accept_15_3_6_1_1_1834 3 171 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 171 211 (accept_3_3 2 171 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 211 (Polychromatic418967fa.accept_13_1_2_3_1_911 1 171 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 171 211)))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 42 170 211 (Eq.refl Bool.true) (allA_of_3_1 42 170 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 43 169 211 (Eq.refl Bool.true) (allA_succ_of_accept 42 169 211 (Polychromatic418967fa.accept_4_2_1_3_1_27
  42 169 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 169 211 (accept_3_3 41
  169 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 169 211
  (Polychromatic418967fa.accept_17_6_16_7_1_12533 40 169 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 169 211 (Polychromatic418967fa.accept_9_3_7_4_1_53 39 169 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 169 211 (accept_3_3 38 169 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 169 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 169 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 169 211
  (Polychromatic418967fa.accept_22_14_15_13_1_10826 36 169 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 169 211 (accept_3_3 35 169 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 169 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 169 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 169 211 (Polychromatic418967fa.accept_9_6_7_4_1_212 33 169 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 169 211 (accept_3_3 32 169 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 169 211 (Polychromatic418967fa.accept_11_9_4_2_1_600
  31 169 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 169 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 169 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 169 211 (accept_3_3 29 169 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 169 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 169 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 169 211 (Polychromatic418967fa.accept_15_12_4_1_1_3746 27 169 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 169 211 (accept_3_3 26 169 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 169 211 (Polychromatic418967fa.accept_10_5_9_1_1_187 25 169
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 169 211
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 169 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 169 211 (accept_3_3 23 169 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 169 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 169 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 169 211 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 169 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 169 211 (accept_3_3 20 169 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 169 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 169 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 169 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 169 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 169 211 (accept_3_3 17 169 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 169 211 (Polychromatic418967fa.accept_19_16_17_2_1_6856 16 169 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 169 211 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 169 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 169 211 (accept_3_3 14 169 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 169 211 (Polychromatic418967fa.accept_23_13_8_4_1_12532 13 169 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 169 211
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 169 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 169 211 (accept_3_3 11 169 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 169 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 169 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 169 211 (Polychromatic418967fa.accept_11_9_4_2_1_600 9 169 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 169 211 (accept_3_3 8 169 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 169 211 (Polychromatic418967fa.accept_16_7_9_3_1_1324 7 169 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 169 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 169 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 169 211 (accept_3_3 5 169 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  169 211 (Polychromatic418967fa.accept_18_4_7_13_1_3303 4 169 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 169 211 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 169 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 169 211 (accept_3_3 2 169 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 169 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 169 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 169 211)))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 44 168 211 (Eq.refl Bool.true) (allA_succ_of_accept 43 168 211 (Polychromatic418967fa.accept_9_7_6_4_1_483
  43 168 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 168 211
  (Polychromatic418967fa.accept_19_4_16_2_1_6967 42 168 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 168 211 (accept_3_3 41 168 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 168 211 (Polychromatic418967fa.accept_22_18_14_13_1_12531 40 168 211 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 168 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 168 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 168 211 (accept_3_3 38 168 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 168 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 168 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 168 211
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 36 168 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 168 211 (accept_3_3 35 168 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 168 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 168 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 168 211 (Polychromatic418967fa.accept_10_3_8_1_1_182 33 168 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 168 211 (accept_3_3 32 168 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 168 211 (Polychromatic418967fa.accept_23_8_7_4_1_12530 31 168
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 168 211
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 168 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 168 211 (accept_3_3 29 168 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 168 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 168 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 168 211 (Polychromatic418967fa.accept_16_11_8_3_1_3183 27 168 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 168 211 (accept_3_3 26 168 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 168 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 168 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 168 211
  (Polychromatic418967fa.accept_19_5_16_2_1_1717 24 168 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 168 211 (accept_3_3 23 168 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 168 211 (Polychromatic418967fa.accept_13_9_12_3_1_907 22 168 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 168 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 168 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 168 211 (accept_3_3 20 168 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 168 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 168 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 168 211
  (Polychromatic418967fa.accept_19_18_16_2_1_2858 18 168 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 168 211 (accept_3_3 17 168 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 168 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 168 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 168 211 (Polychromatic418967fa.accept_13_2_12_3_1_415 15 168
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 168 211 (accept_3_3 14 168
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 168 211
  (Polychromatic418967fa.accept_10_3_8_1_1_182 13 168 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 168 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 168 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 168 211 (accept_3_3 11 168 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 168 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 168 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 168 211 (Polychromatic418967fa.accept_10_9_8_1_1_1331
  9 168 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 168 211 (accept_3_3 8
  168 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 168 211
  (Polychromatic418967fa.accept_9_7_6_4_1_483 7 168 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 168 211 (Polychromatic418967fa.accept_15_6_3_1_1_3678 6 168 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 168 211 (accept_3_3 5 168 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 168 211 (Polychromatic418967fa.accept_13_4_12_3_1_2999 4 168 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 168 211
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 168 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 168 211 (accept_3_3 2 168 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  168 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 168 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 168 211)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 167 211 (Eq.refl Bool.true)
  (allA_of_3_1 45 167 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 46 166 211 (Eq.refl Bool.true)
  (allA_succ_of_accept 45 166 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 166 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 166 211 (accept_3_3 44 166 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 166 211 (Polychromatic418967fa.accept_11_10_1_2_1_1624 43 166 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 166 211
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 166 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 166 211 (accept_3_3 41 166 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 166 211 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 166 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 166 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 166 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 166 211 (accept_3_3 38 166 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 166 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 166 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 166 211
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 36 166 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 166 211 (accept_3_3 35 166 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 166 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 166 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 166 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 166 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 166 211 (accept_3_3 32 166 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 166 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 166 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 166 211
  (Polychromatic418967fa.accept_25_5_16_11_1_12529 30 166 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 166 211 (accept_3_3 29 166 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 166 211 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 166 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 166 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 166 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 166 211 (accept_3_3 26 166 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 166 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 25
  166 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 166 211
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 166 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 166 211 (accept_3_3 23 166 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 166 211 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 166 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 166 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 166 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 166 211 (accept_3_3 20 166 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 166 211 (Polychromatic418967fa.accept_13_6_10_3_1_897 19 166 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 166 211
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 166 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 166 211 (accept_3_3 17 166 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 166 211 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 166 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 166 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 166 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 166 211 (accept_3_3 14 166 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 166 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 166 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 166 211
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 166 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 166 211 (accept_3_3 11 166 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 166 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 166 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 166 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 166 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 166 211 (accept_3_3 8 166 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 166 211 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 166 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 166 211
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 166 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 166 211 (accept_3_3 5 166 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  166 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 166 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 166 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 166 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 166 211 (accept_3_3 2 166 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 166 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 166 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 166 211))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 47 165 211 (Eq.refl Bool.true) (allA_succ_of_accept 46 165 211 (Polychromatic418967fa.accept_4_2_1_3_1_27
  46 165 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 165 211
  (Polychromatic418967fa.accept_7_3_4_1_1_71 45 165 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 165 211 (accept_3_3 44 165 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 165 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 165 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 165 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 165 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 165 211 (accept_3_3 41 165 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 165 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 165 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 165 211
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 39 165 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 165 211 (accept_3_3 38 165 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 165 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 165 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 165 211 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 165 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 165 211 (accept_3_3 35 165 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 165 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 165 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 165 211
  (Polychromatic418967fa.accept_7_5_4_1_1_412 33 165 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 165 211 (accept_3_3 32 165 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 165 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 165 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 165 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 165 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 165 211 (accept_3_3 29 165 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 165 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 165 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 165 211
  (Polychromatic418967fa.accept_12_3_9_7_1_472 27 165 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 165 211 (accept_3_3 26 165 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 165 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 165 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 165 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 165 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 165 211 (accept_3_3 23 165 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 165 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 165 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 165 211
  (Polychromatic418967fa.accept_13_8_9_3_1_2213 21 165 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 165 211 (accept_3_3 20 165 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 165 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 165 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 165 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 165 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 165 211 (accept_3_3 17 165 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 165 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 165 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 165 211
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 165 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 165 211 (accept_3_3 14 165 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 165 211 (Polychromatic418967fa.accept_25_13_15_11_1_8877 13 165 211 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 165 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 165 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 165 211 (accept_3_3 11 165 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 165 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 165 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 165 211
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 165 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 165 211 (accept_3_3 8 165 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  165 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 165 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 165 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 165 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 165 211 (accept_3_3 5 165 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 165 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 165 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 165 211
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 165 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 165 211 (accept_3_3 2 165 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  165 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 165 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 165 211))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 164 211 (Eq.refl
  Bool.true) (allA_of_3_1 48 164 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 163 211 (Eq.refl Bool.true)
  (allA_succ_of_accept 48 163 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 163 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 163 211 (accept_3_3 47 163 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 163 211 (Polychromatic418967fa.accept_18_10_1_13_1_2192 46 163 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 163 211
  (Polychromatic418967fa.accept_7_3_2_1_1_225 45 163 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 163 211 (accept_3_3 44 163 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 163 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 163 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 163 211 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 163 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 163 211 (accept_3_3 41 163 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 163 211 (Polychromatic418967fa.accept_11_7_9_2_1_260 40 163 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 163 211
  (Polychromatic418967fa.accept_9_3_1_4_1_216 39 163 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 163 211 (accept_3_3 38 163 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 163 211 (Polychromatic418967fa.accept_11_4_9_2_1_259 37 163 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 163 211 (Polychromatic418967fa.accept_13_10_7_3_1_3041 36 163 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 163 211 (accept_3_3 35 163 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 163 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 163 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 163 211
  (Polychromatic418967fa.accept_9_6_1_4_1_474 33 163 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 163 211 (accept_3_3 32 163 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 163 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 163 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 163 211 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 163 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 163 211 (accept_3_3 29 163 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 163 211 (Polychromatic418967fa.accept_10_8_3_1_1_1316 28 163 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 163 211
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 163 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 163 211 (accept_3_3 26 163 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 163 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 163 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 163 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 163 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 163 211 (accept_3_3 23 163 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 163 211 (Polychromatic418967fa.accept_10_2_3_1_1_481 22 163 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 163 211
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 163 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 163 211 (accept_3_3 20 163 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 163 211 (Polychromatic418967fa.accept_21_19_16_1_1_2053 19 163 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 163 211 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 163 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 163 211 (accept_3_3 17 163 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 163 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 163 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 163 211
  (Polychromatic418967fa.accept_9_6_1_4_1_474 15 163 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 163 211 (accept_3_3 14 163 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 163 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 163 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 163 211 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 163 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 163 211 (accept_3_3 11 163 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 163 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 163 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 163 211
  (Polychromatic418967fa.accept_13_9_7_3_1_1531 9 163 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 163 211 (accept_3_3 8 163 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  163 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 163 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 163 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 163 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 163 211 (accept_3_3 5 163 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 163 211 (Polychromatic418967fa.accept_11_4_9_2_1_259 4 163 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 163 211
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 163 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 163 211 (accept_3_3 2 163 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  163 211 (Polychromatic418967fa.accept_13_1_7_3_1_1503 1 163 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 163 211))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 162 211 (Eq.refl
  Bool.true) (allA_succ_of_accept 49 162 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 162 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 162 211 (Polychromatic418967fa.accept_13_9_6_3_1_1514
  48 162 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 162 211 (accept_3_3 47
  162 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 162 211
  (Polychromatic418967fa.accept_10_6_2_1_1_494 46 162 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 162 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 162 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 162 211 (accept_3_3 44 162 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 162 211 (Polychromatic418967fa.accept_10_3_2_1_1_839 43 162 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 162 211
  (Polychromatic418967fa.accept_23_19_1_4_1_12528 42 162 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 162 211 (accept_3_3 41 162 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 162 211 (Polychromatic418967fa.accept_13_1_6_3_1_1547 40 162 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 162 211 (Polychromatic418967fa.accept_10_9_2_1_1_840 39 162
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 162 211 (accept_3_3 38 162
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 162 211 (Polychromatic418967fa.accept_4_1_2_3_1_9
  37 162 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 162 211
  (Polychromatic418967fa.accept_10_6_2_1_1_494 36 162 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 162 211 (accept_3_3 35 162 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 162 211 (Polychromatic418967fa.accept_15_4_12_1_1_1081 34 162 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 162 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 162 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 162 211 (accept_3_3 32 162 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 162 211 (Polychromatic418967fa.accept_13_5_6_3_1_868 31 162 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 162 211
  (Polychromatic418967fa.accept_14_2_8_1_1_1647 30 162 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 162 211 (accept_3_3 29 162 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 162 211 (Polychromatic418967fa.accept_15_13_12_1_1_1841 28 162 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 162 211 (Polychromatic418967fa.accept_11_5_8_2_1_588 27 162 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 162 211 (accept_3_3 26 162 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 162 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 162 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 162 211
  (Polychromatic418967fa.accept_19_5_10_2_1_1731 24 162 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 162 211 (accept_3_3 23 162 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 162 211 (Polychromatic418967fa.accept_13_9_6_3_1_1514 22 162 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 162 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 162 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 162 211 (accept_3_3 20 162 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 162 211 (Polychromatic418967fa.accept_10_9_2_1_1_840 19 162 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 162 211
  (Polychromatic418967fa.accept_13_5_6_3_1_868 18 162 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 162 211 (accept_3_3 17 162 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 162 211 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 162 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 162 211 (Polychromatic418967fa.accept_16_15_2_3_1_4262 15 162 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 162 211 (accept_3_3 14 162 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 162 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 162 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 162 211
  (Polychromatic418967fa.accept_19_12_10_2_1_12527 12 162 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 162 211 (accept_3_3 11 162 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 162 211 (Polychromatic418967fa.accept_13_10_6_3_1_1515 10 162 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 162 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 162 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 162 211 (accept_3_3 8 162 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 162 211 (Polychromatic418967fa.accept_14_7_8_1_1_1621
  7 162 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 162 211
  (Polychromatic418967fa.accept_10_6_2_1_1_494 6 162 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 162 211 (accept_3_3 5 162 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  162 211 (Polychromatic418967fa.accept_15_4_12_1_1_1081 4 162 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 162 211 (Polychromatic418967fa.accept_10_3_2_1_1_839 3 162 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 162 211 (accept_3_3 2 162 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 162 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 162 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162
  211)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 161 211 (Eq.refl Bool.true) (allA_of_3_1 51 161
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 52 160 211 (Eq.refl Bool.true) (allA_succ_of_accept 51 160
  211 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 160 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 160 211 (accept_3_3 50 160 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 160 211 (Polychromatic418967fa.accept_14_7_6_1_1_1656 49 160 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 160 211 (Polychromatic418967fa.accept_9_3_7_4_1_53 48 160 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 160 211 (accept_3_3 47 160 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 160 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 160 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 160 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 160 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 160 211 (accept_3_3 44 160 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 160 211 (Polychromatic418967fa.accept_15_13_10_1_1_1862 43 160 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 160 211 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 160 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 160 211 (accept_3_3 41 160 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 160 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 160 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 160 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 160 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 160 211 (accept_3_3 38 160 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 160 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 160 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 160 211 (Polychromatic418967fa.accept_15_6_10_1_1_3675 36 160 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 160 211 (accept_3_3 35 160 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 160 211 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 160
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 160 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 160 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 160 211 (accept_3_3 32 160 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 160 211 (Polychromatic418967fa.accept_21_10_13_1_1_11019 31 160 211 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 160 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 160 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 160 211 (accept_3_3 29 160 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 160 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 160 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 160 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 160 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 160 211 (accept_3_3 26 160 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 160 211 (Polychromatic418967fa.accept_13_12_4_3_1_1528 25 160 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 160 211 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 160 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 160 211 (accept_3_3 23 160 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 160 211 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 160 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 160 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 160 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 160 211 (accept_3_3 20 160 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 160 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 160 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 160 211 (Polychromatic418967fa.accept_22_18_6_13_1_7751 18 160 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 160 211 (accept_3_3 17 160 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 160 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 160 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 160 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 160 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 160 211 (accept_3_3 14 160 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 160 211 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 160 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 160 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 160 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 160 211 (accept_3_3 11 160 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 160 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 160 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 160 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 160 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 160 211 (accept_3_3 8 160 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  160 211 (Polychromatic418967fa.accept_13_7_4_3_1_3064 7 160 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 160 211 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 160 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 160 211 (accept_3_3 5 160 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 160 211 (Polychromatic418967fa.accept_11_4_6_2_1_51 4 160 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 160 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 160 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 160 211 (accept_3_3 2 160 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  160 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 160 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 160 211)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 159 211 (Eq.refl
  Bool.true) (allA_succ_of_accept 52 159 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 159 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 159 211 (Polychromatic418967fa.accept_15_6_9_1_1_1823
  51 159 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 159 211 (accept_3_3 50
  159 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 159 211
  (Polychromatic418967fa.accept_21_7_12_1_1_952 49 159 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 159 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 159 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 159 211 (accept_3_3 47 159 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 159 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 159 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 159 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 45
  159 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 159 211 (accept_3_3 44
  159 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 159 211
  (Polychromatic418967fa.accept_9_7_6_4_1_483 43 159 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 159 211 (Polychromatic418967fa.accept_10_2_9_1_1_185 42 159 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 159 211 (accept_3_3 41 159 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 159 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 159 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 159 211 (Polychromatic418967fa.accept_7_4_5_1_1_418
  39 159 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 159 211 (accept_3_3 38
  159 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 159 211
  (Polychromatic418967fa.accept_9_1_6_4_1_49 37 159 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 159 211 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 159 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 159 211 (accept_3_3 35 159 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 159 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 159 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 159 211 (Polychromatic418967fa.accept_12_9_3_7_1_924
  33 159 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 159 211 (accept_3_3 32
  159 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 159 211
  (Polychromatic418967fa.accept_7_3_5_1_1_72 31 159 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 159 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 30 159 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 159 211 (accept_3_3 29 159 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 159 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 159 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 159 211 (Polychromatic418967fa.accept_7_6_5_1_1_416
  27 159 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 159 211 (accept_3_3 26
  159 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 159 211
  (Polychromatic418967fa.accept_7_4_5_1_1_418 25 159 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 159 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 159 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 159 211 (accept_3_3 23 159 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 159 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 159 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 159 211 (Polychromatic418967fa.accept_9_3_6_4_1_210
  21 159 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 159 211 (accept_3_3 20
  159 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 159 211
  (Polychromatic418967fa.accept_9_1_6_4_1_49 19 159 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 159 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 159 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 159 211 (accept_3_3 17 159 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 159 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 159 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 159 211 (Polychromatic418967fa.accept_10_5_9_1_1_187
  15 159 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 159 211 (accept_3_3 14
  159 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 211
  (Polychromatic418967fa.accept_7_6_5_1_1_416 13 159 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 159 211 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 159 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 159 211 (accept_3_3 11 159 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 159 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 159 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 159 211 (Polychromatic418967fa.accept_12_9_3_7_1_924 9
  159 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 159 211 (accept_3_3 8 159
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 211
  (Polychromatic418967fa.accept_9_7_6_4_1_483 7 159 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 159 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 159 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 159 211 (accept_3_3 5 159 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 159 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 159 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 159 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 3
  159 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 159 211 (accept_3_3 2 159
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 211 (Polychromatic418967fa.accept_9_1_6_4_1_49
  1 159 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 159
  211))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 158 211 (Eq.refl Bool.true) (allA_of_3_1 54
  158 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 55 157 211 (Eq.refl Bool.true) (allA_succ_of_accept 54
  157 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 157 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 157 211 (accept_3_3 53 157 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 157 211 (Polychromatic418967fa.accept_19_14_5_2_1_6941 52 157 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 157 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 157 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 157 211 (accept_3_3 50 157 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 157 211
  (Polychromatic418967fa.accept_16_1_13_3_1_2168 49 157 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 157 211 (Polychromatic418967fa.accept_17_14_4_7_1_7439 48 157 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 157 211 (accept_3_3 47 157 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 157 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 157 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 157 211 (Polychromatic418967fa.accept_11_1_3_2_1_1090
  45 157 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 157 211 (accept_3_3 44
  157 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 157 211
  (Polychromatic418967fa.accept_13_4_1_3_1_3058 43 157 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 157 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 157 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 157 211 (accept_3_3 41 157 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 157 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 157 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 157 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 39
  157 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 157 211 (accept_3_3 38
  157 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 157 211
  (Polychromatic418967fa.accept_7_2_3_1_1_10 37 157 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 157 211 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 157 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 157 211 (accept_3_3 35 157 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 157 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 157 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 157 211 (Polychromatic418967fa.accept_7_5_3_1_1_424
  33 157 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 157 211 (accept_3_3 32
  157 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 157 211
  (Polychromatic418967fa.accept_13_5_1_3_1_878 31 157 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 157 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 157 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 157 211 (accept_3_3 29 157 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 157 211 (Polychromatic418967fa.accept_13_2_1_3_1_419 28 157 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 157 211
  (Polychromatic418967fa.accept_19_8_5_2_1_4105 27 157 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 157 211 (accept_3_3 26 157 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 157 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 157 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 157 211 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 157 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 157 211 (accept_3_3 23 157 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 157 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 157 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 157 211
  (Polychromatic418967fa.accept_15_6_7_1_1_93 21 157 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 157 211 (accept_3_3 20 157 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 157 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 157 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 157 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 157 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 157 211 (accept_3_3 17 157 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 157 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 157 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 157 211
  (Polychromatic418967fa.accept_13_2_1_3_1_419 15 157 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 157 211 (accept_3_3 14 157 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 157 211 (Polychromatic418967fa.accept_21_13_10_1_1_6292 13 157 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 157 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 157 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 157 211 (accept_3_3 11 157 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 157 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 157 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 157 211
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 157 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 157 211 (accept_3_3 8 157 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  157 211 (Polychromatic418967fa.accept_13_7_1_3_1_1523 7 157 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 157 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 157 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 157 211 (accept_3_3 5 157 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 157 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 157 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 157 211
  (Polychromatic418967fa.accept_17_3_4_7_1_1658 3 157 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 157 211 (accept_3_3 2 157 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  157 211 (Polychromatic418967fa.accept_11_1_3_2_1_1090 1 157 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 157 211))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 156 211 (Eq.refl
  Bool.true) (allA_succ_of_accept 55 156 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 55 156 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 156 211 (Polychromatic418967fa.accept_15_9_6_1_1_493
  54 156 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 156 211 (accept_3_3 53
  156 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 156 211
  (Polychromatic418967fa.accept_7_3_2_1_1_225 52 156 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 156 211 (Polychromatic418967fa.accept_9_6_3_4_1_477 51 156 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 156 211 (accept_3_3 50 156 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 156 211 (Polychromatic418967fa.accept_19_11_4_2_1_1700 49 156 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 156 211
  (Polychromatic418967fa.accept_7_6_2_1_1_214 48 156 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 156 211 (accept_3_3 47 156 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 156 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 156 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 156 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 156 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 156 211 (accept_3_3 44 156 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 156 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 156 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 156 211
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 156 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 156 211 (accept_3_3 41 156 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 156 211 (Polychromatic418967fa.accept_15_10_6_1_1_3707 40 156 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 156 211 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 156 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 156 211 (accept_3_3 38 156 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 156 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 156 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 156 211
  (Polychromatic418967fa.accept_14_8_2_1_1_1652 36 156 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 156 211 (accept_3_3 35 156 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 156 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 156 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 156 211 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 156 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 156 211 (accept_3_3 32 156 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 156 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 156 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 156 211
  (Polychromatic418967fa.accept_19_11_4_2_1_1700 30 156 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 156 211 (accept_3_3 29 156 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 156 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 156 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 156 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 156 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 156 211 (accept_3_3 26 156 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 156 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 156 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 156 211
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 156 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 156 211 (accept_3_3 23 156 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 156 211 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 156 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 156 211 (Polychromatic418967fa.accept_17_4_3_7_1_4971 21 156 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 156 211 (accept_3_3 20 156 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 156 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 156 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 156 211
  (Polychromatic418967fa.accept_15_3_6_1_1_1834 18 156 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 156 211 (accept_3_3 17 156 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 156 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 156 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 156 211 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 156 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 156 211 (accept_3_3 14 156 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 156 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 156 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 156 211
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 156 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 156 211 (accept_3_3 11 156 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 156 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 156 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 156 211 (Polychromatic418967fa.accept_15_9_6_1_1_493 9 156 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 156 211 (accept_3_3 8 156 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 156 211 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 156 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 156 211
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 156 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 156 211 (accept_3_3 5 156 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  156 211 (Polychromatic418967fa.accept_16_4_12_3_1_2180 4 156 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 156 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 156 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 156 211 (accept_3_3 2 156 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 156 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 156 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156
  211)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 155 211 (Eq.refl Bool.true) (allA_of_3_1 57
  155 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 58 154 211 (Eq.refl Bool.true) (allA_succ_of_accept 57
  154 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 154 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 154 211 (accept_3_3 56 154 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 154 211 (Polychromatic418967fa.accept_10_5_4_1_1_842 55 154 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 154 211 (Polychromatic418967fa.accept_13_2_11_3_1_873 54 154
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 154 211 (accept_3_3 53 154
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 154 211
  (Polychromatic418967fa.accept_9_7_1_4_1_217 52 154 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 154 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 154 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 154 211 (accept_3_3 50 154 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 154 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 154 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 154 211 (Polychromatic418967fa.accept_9_3_1_4_1_216
  48 154 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 154 211 (accept_3_3 47
  154 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 154 211
  (Polychromatic418967fa.accept_13_7_11_3_1_1540 46 154 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 154 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 154 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 154 211 (accept_3_3 44 154 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 154 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 154 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 154 211 (Polychromatic418967fa.accept_9_6_1_4_1_474
  42 154 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 154 211 (accept_3_3 41
  154 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 154 211
  (Polychromatic418967fa.accept_12_4_10_7_1_149 40 154 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 154 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 154 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 154 211 (accept_3_3 38 154 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 154 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 154 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 154 211
  (Polychromatic418967fa.accept_13_10_11_3_1_1518 36 154 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 154 211 (accept_3_3 35 154 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 154 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 154 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 154 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 154 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 154 211 (accept_3_3 32 154 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 154 211 (Polychromatic418967fa.accept_13_5_11_3_1_902
  31 154 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 154 211
  (Polychromatic418967fa.accept_9_3_1_4_1_216 30 154 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 154 211 (accept_3_3 29 154 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 154 211 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 154 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 154 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 154 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 154 211 (accept_3_3 26 154 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 154 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 154 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 154 211
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 154 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 154 211 (accept_3_3 23 154 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 154 211 (Polychromatic418967fa.accept_18_4_10_13_1_5883 22 154 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 154 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 154 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 154 211 (accept_3_3 20 154 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 154 211 (Polychromatic418967fa.accept_18_1_10_13_1_500 19 154 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 154 211
  (Polychromatic418967fa.accept_13_5_11_3_1_902 18 154 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 154 211 (accept_3_3 17 154 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 154 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 154 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 154 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 154 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 154 211 (accept_3_3 14 154 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 154 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 154 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 154 211
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 154 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 154 211 (accept_3_3 11 154 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 154 211 (Polychromatic418967fa.accept_13_10_11_3_1_1518 10 154 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 154 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 154 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 154 211 (accept_3_3 8 154 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 154 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 154 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 154 211
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 154 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 154 211 (accept_3_3 5 154 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  154 211 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 154 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 154 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 154 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 154 211 (accept_3_3 2 154 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 154 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 154 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 154
  211)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 153 211 (Eq.refl Bool.true)
  (allA_succ_of_accept 58 153 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 153 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 153 211 (Polychromatic418967fa.accept_18_3_9_13_1_1235 57 153
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 153 211 (accept_3_3 56 153
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 153 211
  (Polychromatic418967fa.accept_16_7_9_3_1_1324 55 153 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 153 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 153 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 153 211 (accept_3_3 53 153 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 153 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 153 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 153 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 51
  153 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 153 211 (accept_3_3 50
  153 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 153 211
  (Polychromatic418967fa.accept_14_7_13_1_1_922 49 153 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 153 211 (Polychromatic418967fa.accept_10_8_3_1_1_1316 48 153 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 153 211 (accept_3_3 47 153 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 153 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 153 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 153 211 (Polychromatic418967fa.accept_11_1_10_2_1_58
  45 153 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 153 211 (accept_3_3 44
  153 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 153 211
  (Polychromatic418967fa.accept_15_13_3_1_1_3740 43 153 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 153 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 153 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 153 211 (accept_3_3 41 153 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 153 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 153 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 153 211 (Polychromatic418967fa.accept_12_3_9_7_1_472
  39 153 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 153 211 (accept_3_3 38
  153 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 153 211
  (Polychromatic418967fa.accept_7_2_6_1_1_73 37 153 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 153 211 (Polychromatic418967fa.accept_15_6_3_1_1_3678 36 153 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 153 211 (accept_3_3 35 153 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 153 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 153 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 153 211 (Polychromatic418967fa.accept_7_5_6_1_1_407
  33 153 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 153 211 (accept_3_3 32
  153 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 153 211
  (Polychromatic418967fa.accept_19_12_1_2_1_9750 31 153 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 153 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 153 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 153 211 (accept_3_3 29 153 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 153 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 153 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 153 211 (Polychromatic418967fa.accept_12_3_9_7_1_472
  27 153 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 153 211 (accept_3_3 26
  153 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 153 211
  (Polychromatic418967fa.accept_19_6_1_2_1_12526 25 153 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 153 211 (Polychromatic418967fa.accept_13_11_10_3_1_3020 24 153 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 153 211 (accept_3_3 23 153 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 153 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 153 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 153 211
  (Polychromatic418967fa.accept_14_7_13_1_1_922 21 153 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 153 211 (accept_3_3 20 153 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 153 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 153 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 153 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 153 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 153 211 (accept_3_3 17 153 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 153 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 153 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 153 211
  (Polychromatic418967fa.accept_12_3_9_7_1_472 15 153 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 153 211 (accept_3_3 14 153 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 153 211 (Polychromatic418967fa.accept_15_13_3_1_1_3740 13 153 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 153 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 153 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 153 211 (accept_3_3 11 153 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 153 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 153 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 153 211
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 153 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 153 211 (accept_3_3 8 153 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  153 211 (Polychromatic418967fa.accept_13_7_10_3_1_1505 7 153 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 153 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 153 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 153 211 (accept_3_3 5 153 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 153 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 153 211
  (Polychromatic418967fa.accept_12_3_9_7_1_472 3 153 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 153 211 (accept_3_3 2 153 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  153 211 (Polychromatic418967fa.accept_11_1_10_2_1_58 1 153 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 153 211))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 152 211
  (Eq.refl Bool.true) (allA_of_3_1 60 152 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 61 151 211 (Eq.refl
  Bool.true) (allA_succ_of_accept 60 151 211 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 151 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 151 211 (accept_3_3 59 151 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 151 211 (Polychromatic418967fa.accept_16_10_7_3_1_6601 58 151 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 151 211
  (Polychromatic418967fa.accept_9_3_7_4_1_53 57 151 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 151 211 (accept_3_3 56 151 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 151 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 151 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 151 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 151 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 151 211 (accept_3_3 53 151 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 151 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 151 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 151 211
  (Polychromatic418967fa.accept_9_6_7_4_1_212 51 151 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 151 211 (accept_3_3 50 151 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 151 211 (Polychromatic418967fa.accept_11_5_8_2_1_588 49 151 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 151 211 (Polychromatic418967fa.accept_9_3_7_4_1_53 48 151 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 151 211 (accept_3_3 47 151 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 151 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 151 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 151 211
  (Polychromatic418967fa.accept_7_3_4_1_1_71 45 151 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 151 211 (accept_3_3 44 151 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 151 211 (Polychromatic418967fa.accept_16_11_7_3_1_3163 43 151 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 151 211 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 151 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 151 211 (accept_3_3 41 151 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 151 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 40 151 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 151 211
  (Polychromatic418967fa.accept_9_3_7_4_1_53 39 151 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 151 211 (accept_3_3 38 151 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 151 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 151 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 151 211 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 151 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 151 211 (accept_3_3 35 151 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 151 211 (Polychromatic418967fa.accept_19_15_18_2_1_6857 34 151 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 151 211
  (Polychromatic418967fa.accept_7_5_4_1_1_412 33 151 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 151 211 (accept_3_3 32 151 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 151 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 151 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 151 211 (Polychromatic418967fa.accept_9_3_7_4_1_53 30 151 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 151 211 (accept_3_3 29 151 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 151 211 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 151 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 151 211
  (Polychromatic418967fa.accept_11_5_8_2_1_588 27 151 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 151 211 (accept_3_3 26 151 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 151 211 (Polychromatic418967fa.accept_16_9_7_3_1_614 25 151 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 151 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 151 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 151 211 (accept_3_3 23 151 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 151 211 (Polychromatic418967fa.accept_13_9_8_3_1_3045 22 151 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 151 211
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 151 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 151 211 (accept_3_3 20 151 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 151 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 151 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 151 211 (Polychromatic418967fa.accept_13_5_8_3_1_1535 18 151 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 151 211 (accept_3_3 17 151 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 151 211 (Polychromatic418967fa.accept_11_5_8_2_1_588 16 151
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 151 211
  (Polychromatic418967fa.accept_9_6_7_4_1_212 15 151 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 151 211 (accept_3_3 14 151 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 151 211 (Polychromatic418967fa.accept_21_13_4_1_1_942 13 151 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 151 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 151 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 151 211 (accept_3_3 11 151 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 151 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 151 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 151 211
  (Polychromatic418967fa.accept_13_9_8_3_1_3045 9 151 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 151 211 (accept_3_3 8 151 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  151 211 (Polychromatic418967fa.accept_13_7_8_3_1_1533 7 151 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 151 211 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 151 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 151 211 (accept_3_3 5 151 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 151 211 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 151 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 151 211
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 151 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 151 211 (accept_3_3 2 151 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  151 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 151 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 151 211))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 150 211
  (Eq.refl Bool.true) (allA_succ_of_accept 61 150 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 150 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 150 211
  (Polychromatic418967fa.accept_7_4_3_1_1_87 60 150 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 150 211 (accept_3_3 59 150 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 150 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 58 150 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 150 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 150 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 150 211 (accept_3_3 56 150 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 150 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 55 150 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 150 211
  (Polychromatic418967fa.accept_7_5_3_1_1_424 54 150 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 150 211 (accept_3_3 53 150 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 150 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 52 150 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 150 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 150 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 150 211 (accept_3_3 50 150 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 150 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 150 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 150 211
  (Polychromatic418967fa.accept_9_3_6_4_1_210 48 150 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 150 211 (accept_3_3 47 150 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 150 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 46 150 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 150 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 150 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 150 211 (accept_3_3 44 150 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 150 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 150 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 150 211
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 42 150 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 150 211 (accept_3_3 41 150 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 150 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 150 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 150 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 150 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 150 211 (accept_3_3 38 150 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 150 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 150 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 150 211
  (Polychromatic418967fa.accept_13_10_7_3_1_3041 36 150 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 150 211 (accept_3_3 35 150 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 150 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 150 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 150 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 150 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 150 211 (accept_3_3 32 150 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 150 211 (Polychromatic418967fa.accept_11_9_7_2_1_1068 31 150 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 150 211
  (Polychromatic418967fa.accept_7_2_3_1_1_10 30 150 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 150 211 (accept_3_3 29 150 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 150 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 150 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 150 211 (Polychromatic418967fa.accept_13_1_7_3_1_1503 27 150 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 150 211 (accept_3_3 26 150 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 150 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 150 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 150 211
  (Polychromatic418967fa.accept_13_11_7_3_1_894 24 150 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 150 211 (accept_3_3 23 150 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 150 211 (Polychromatic418967fa.accept_13_9_7_3_1_1531 22 150 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 150 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 150 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 150 211 (accept_3_3 20 150 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 150 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 150 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 150 211
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 150 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 150 211 (accept_3_3 17 150 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 150 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 150 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 150 211 (Polychromatic418967fa.accept_19_15_17_2_1_4097 15 150 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 150 211 (accept_3_3 14 150 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 150 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 150 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 150 211
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 150 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 150 211 (accept_3_3 11 150 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 150 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 150 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 150 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 150 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 150 211 (accept_3_3 8 150 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 150 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 150 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 150 211
  (Polychromatic418967fa.accept_17_6_14_7_1_6115 6 150 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 150 211 (accept_3_3 5 150 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  150 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 150 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 150 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 150 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 150 211 (accept_3_3 2 150 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 150 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 150 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  211)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 149 211 (Eq.refl Bool.true)
  (allA_of_3_1 63 149 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 64 148 211 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 148 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 148 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 148 211 (accept_3_3 62 148 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 148 211 (Polychromatic418967fa.accept_13_9_5_3_1_428 61 148 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 148 211
  (Polychromatic418967fa.accept_13_8_5_3_1_427 60 148 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 148 211 (accept_3_3 59 148 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 148 211 (Polychromatic418967fa.accept_12_10_4_7_1_948 58 148 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 148 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 148 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 148 211 (accept_3_3 56 148 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 148 211 (Polychromatic418967fa.accept_8_7_4_3_1_156 55 148 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 148 211
  (Polychromatic418967fa.accept_13_2_5_3_1_406 54 148 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 148 211 (accept_3_3 53 148 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 148 211 (Polychromatic418967fa.accept_11_8_5_2_1_1629 52 148 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 148 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 148 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 148 211 (accept_3_3 50 148 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 148 211 (Polychromatic418967fa.accept_10_9_8_1_1_1331 49 148 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 148 211
  (Polychromatic418967fa.accept_13_9_5_3_1_428 48 148 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 148 211 (accept_3_3 47 148 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 148 211 (Polychromatic418967fa.accept_12_10_4_7_1_948 46 148 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 148 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 148 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 148 211 (accept_3_3 44 148 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 148 211 (Polychromatic418967fa.accept_10_3_8_1_1_182 43 148 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 148 211
  (Polychromatic418967fa.accept_15_12_13_1_1_3695 42 148 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 148 211 (accept_3_3 41 148 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 148 211 (Polychromatic418967fa.accept_13_1_5_3_1_888 40 148 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 148 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 148 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 148 211 (accept_3_3 38 148 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 148 211 (Polychromatic418967fa.accept_13_11_5_3_1_889
  37 148 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 148 211
  (Polychromatic418967fa.accept_17_2_12_7_1_7429 36 148 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 148 211 (accept_3_3 35 148 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 148 211 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 148 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 148 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 148 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 148 211 (accept_3_3 32 148 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 148 211 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 148 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 148 211
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 30 148 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 148 211 (accept_3_3 29 148 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 148 211 (Polychromatic418967fa.accept_13_2_5_3_1_406 28 148 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 148 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 148 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 148 211 (accept_3_3 26 148 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 148 211 (Polychromatic418967fa.accept_15_10_13_1_1_3698 25 148 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 148 211
  (Polychromatic418967fa.accept_13_11_5_3_1_889 24 148 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 148 211 (accept_3_3 23 148 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 148 211 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 148 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 148 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 148 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 148 211 (accept_3_3 20 148 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 148 211 (Polychromatic418967fa.accept_10_9_8_1_1_1331 19 148 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 148 211
  (Polychromatic418967fa.accept_15_3_13_1_1_479 18 148 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 148 211 (accept_3_3 17 148 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 148 211 (Polychromatic418967fa.accept_14_2_8_1_1_1647 16 148 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 148 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 148 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 148 211 (accept_3_3 14 148 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 148 211 (Polychromatic418967fa.accept_10_3_8_1_1_182 13 148 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 148 211
  (Polychromatic418967fa.accept_15_12_13_1_1_3695 12 148 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 148 211 (accept_3_3 11 148 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 148 211 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 148 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 148 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 148 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 148 211 (accept_3_3 8 148 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 148 211 (Polychromatic418967fa.accept_8_7_4_3_1_156 7
  148 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 148 211
  (Polychromatic418967fa.accept_13_6_5_3_1_426 6 148 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 148 211 (accept_3_3 5 148 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  148 211 (Polychromatic418967fa.accept_17_4_12_7_1_8771 4 148 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 148 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 148 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 148 211 (accept_3_3 2 148 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 148 211 (Polychromatic418967fa.accept_13_1_5_3_1_888 1 148 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 148
  211)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 147 211 (Eq.refl Bool.true)
  (allA_succ_of_accept 64 147 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 147 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 147 211 (Polychromatic418967fa.accept_18_9_3_13_1_5905 63 147
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 147 211 (accept_3_3 62 147
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 147 211
  (Polychromatic418967fa.accept_9_7_3_4_1_218 61 147 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 147 211 (Polychromatic418967fa.accept_9_6_3_4_1_477 60 147 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 147 211 (accept_3_3 59 147 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 147 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 147 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 147 211 (Polychromatic418967fa.accept_12_9_3_7_1_924
  57 147 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 147 211 (accept_3_3 56
  147 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 147 211
  (Polychromatic418967fa.accept_9_1_3_4_1_47 55 147 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 147 211 (Polychromatic418967fa.accept_10_4_7_1_1_471 54 147 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 147 211 (accept_3_3 53 147 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 147 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 147 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 147 211 (Polychromatic418967fa.accept_9_6_3_4_1_477
  51 147 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 147 211 (accept_3_3 50
  147 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 147 211
  (Polychromatic418967fa.accept_15_4_12_1_1_1081 49 147 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 147 211 (Polychromatic418967fa.accept_14_6_7_1_1_78 48 147 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 147 211 (accept_3_3 47 147 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 147 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 147 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 147 211 (Polychromatic418967fa.accept_12_9_3_7_1_924
  45 147 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 147 211 (accept_3_3 44
  147 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 147 211
  (Polychromatic418967fa.accept_9_7_3_4_1_218 43 147 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 147 211 (Polychromatic418967fa.accept_9_6_3_4_1_477 42 147 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 147 211 (accept_3_3 41 147 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 147 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 147 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 147 211 (Polychromatic418967fa.accept_11_6_4_2_1_599
  39 147 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 147 211 (accept_3_3 38
  147 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 147 211
  (Polychromatic418967fa.accept_9_1_3_4_1_47 37 147 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 147 211 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 147 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 147 211 (accept_3_3 35 147 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 147 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 147 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 147 211 (Polychromatic418967fa.accept_9_6_3_4_1_477
  33 147 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 147 211 (accept_3_3 32
  147 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 147 211
  (Polychromatic418967fa.accept_11_9_4_2_1_600 31 147 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 147 211 (Polychromatic418967fa.accept_17_13_11_7_1_4961 30 147 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 147 211 (accept_3_3 29 147 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 147 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 147 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 147 211
  (Polychromatic418967fa.accept_13_1_4_3_1_1545 27 147 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 147 211 (accept_3_3 26 147 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 147 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 147 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 147 211 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 147 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 147 211 (accept_3_3 23 147 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 147 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 147 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 147 211
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 147 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 147 211 (accept_3_3 20 147 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 147 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 147 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 147 211 (Polychromatic418967fa.accept_17_1_11_7_1_4962 18 147 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 147 211 (accept_3_3 17 147 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 147 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 147 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 147 211
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 147 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 147 211 (accept_3_3 14 147 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 147 211 (Polychromatic418967fa.accept_14_13_7_1_1_1618 13 147 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 147 211 (Polychromatic418967fa.accept_13_12_4_3_1_1528 12 147 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 147 211 (accept_3_3 11 147 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 147 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 147 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 147 211
  (Polychromatic418967fa.accept_11_9_4_2_1_600 9 147 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 147 211 (accept_3_3 8 147 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  147 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 147 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 147 211 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 147 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 147 211 (accept_3_3 5 147 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 147 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 147 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 147 211
  (Polychromatic418967fa.accept_27_3_12_22_1_12525 3 147 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 147 211 (accept_3_3 2 147 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 147 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 147 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 147 211)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 66 146 211 (Eq.refl Bool.true) (allA_of_3_1 66 146 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 67 145 211 (Eq.refl Bool.true) (allA_succ_of_accept 66 145 211 (Polychromatic418967fa.accept_4_2_1_3_1_27
  66 145 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 145 211 (accept_3_3 65
  145 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 145 211
  (Polychromatic418967fa.accept_10_4_5_1_1_497 64 145 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 145 211 (Polychromatic418967fa.accept_13_11_2_3_1_883 63 145 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 145 211 (accept_3_3 62 145 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 145 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 145 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 145 211 (Polychromatic418967fa.accept_7_4_5_1_1_418
  60 145 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 145 211 (accept_3_3 59
  145 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 145 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 58 145 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 145 211 (Polychromatic418967fa.accept_9_3_1_4_1_216 57 145 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 145 211 (accept_3_3 56 145 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 145 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 55 145 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 145 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 54
  145 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 145 211 (accept_3_3 53
  145 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 145 211
  (Polychromatic418967fa.accept_7_3_5_1_1_72 52 145 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 145 211 (Polychromatic418967fa.accept_9_6_1_4_1_474 51 145 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 145 211 (accept_3_3 50 145 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 145 211 (Polychromatic418967fa.accept_10_9_5_1_1_1325 49 145 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 145 211
  (Polychromatic418967fa.accept_7_6_5_1_1_416 48 145 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 145 211 (accept_3_3 47 145 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 145 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 145 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 145 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 145 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 145 211 (accept_3_3 44 145 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 145 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 145 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 145 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 145 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 145 211 (accept_3_3 41 145 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 145 211 (Polychromatic418967fa.accept_13_1_2_3_1_911 40 145 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 145 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 145 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 145 211 (accept_3_3 38 145 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 145 211 (Polychromatic418967fa.accept_13_11_2_3_1_883 37 145 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 145 211
  (Polychromatic418967fa.accept_10_6_5_1_1_482 36 145 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 145 211 (accept_3_3 35 145 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 145 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 145 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 145 211 (Polychromatic418967fa.accept_9_6_1_4_1_474 33 145 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 145 211 (accept_3_3 32 145 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 145 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 145 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 145 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 145 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 145 211 (accept_3_3 29 145 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 145 211 (Polychromatic418967fa.accept_15_13_10_1_1_1862 28 145 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 145 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 145 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 145 211 (accept_3_3 26 145 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 145 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 145 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 145 211
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 145 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 145 211 (accept_3_3 23 145 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 145 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 145 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 145 211 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 145 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 145 211 (accept_3_3 20 145 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 145 211 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 145 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 145 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 145 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 145 211 (accept_3_3 17 145 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 145 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 145 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 145 211 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 145 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 145 211 (accept_3_3 14 145 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 145 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 145 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 145 211
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 145 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 145 211 (accept_3_3 11 145 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 145 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 145 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 145 211 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 145 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 145 211 (accept_3_3 8 145 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 145 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 145 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 145 211
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 145 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 145 211 (accept_3_3 5 145 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  145 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 145 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 145 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 145 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 145 211 (accept_3_3 2 145 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 145 211 (Polychromatic418967fa.accept_13_1_2_3_1_911 1 145 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 145
  211))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 144 211 (Eq.refl Bool.true)
  (allA_succ_of_accept 67 144 211 (Polychromatic418967fa.accept_10_7_4_1_1_1319 67 144 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 144 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 66 144 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 144 211 (accept_3_3 65 144 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 144 211
  (Polychromatic418967fa.accept_26_12_14_3_1_12524 64 144 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 144 211 (Polychromatic418967fa.accept_13_11_1_3_1_910 63 144 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 144 211 (accept_3_3 62 144 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 144 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 61 144 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 144 211
  (Polychromatic418967fa.accept_19_3_11_2_1_12523 60 144 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 144 211 (accept_3_3 59 144 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 144 211 (Polychromatic418967fa.accept_11_3_1_2_1_1063 58 144 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 144 211 (Polychromatic418967fa.accept_10_7_4_1_1_1319 57 144
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 144 211 (accept_3_3 56 144
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 144 211
  (Polychromatic418967fa.accept_10_5_4_1_1_842 55 144 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 144 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 144 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 144 211 (accept_3_3 53 144 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 144 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 144 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 144 211 (Polychromatic418967fa.accept_15_6_9_1_1_1823
  51 144 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 144 211 (accept_3_3 50
  144 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 144 211
  (Polychromatic418967fa.accept_23_3_6_4_1_12522 49 144 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 144 211 (Polychromatic418967fa.accept_17_14_8_7_1_6183 48 144 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 144 211 (accept_3_3 47 144 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 144 211 (Polychromatic418967fa.accept_13_7_1_3_1_1523 46 144 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 144 211
  (Polychromatic418967fa.accept_7_3_4_1_1_71 45 144 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 144 211 (accept_3_3 44 144 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 144 211 (Polychromatic418967fa.accept_11_10_1_2_1_1624 43 144 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 144 211 (Polychromatic418967fa.accept_19_4_11_2_1_11111 42 144 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 144 211 (accept_3_3 41 144 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 144 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 40 144 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 144 211
  (Polychromatic418967fa.accept_14_11_4_1_1_4255 39 144 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 144 211 (accept_3_3 38 144 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 144 211 (Polychromatic418967fa.accept_10_7_4_1_1_1319 37 144 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 144 211 (Polychromatic418967fa.accept_11_3_1_2_1_1063 36 144 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 144 211 (accept_3_3 35 144 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 144 211 (Polychromatic418967fa.accept_19_15_11_2_1_12506 34
  144 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 144 211
  (Polychromatic418967fa.accept_7_5_4_1_1_412 33 144 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 144 211 (accept_3_3 32 144 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 144 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 144 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 144 211 (Polychromatic418967fa.accept_13_4_1_3_1_3058 30 144 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 144 211 (accept_3_3 29 144 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 144 211 (Polychromatic418967fa.accept_13_2_1_3_1_419 28 144
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 144 211
  (Polychromatic418967fa.accept_10_7_4_1_1_1319 27 144 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 144 211 (accept_3_3 26 144 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 144 211 (Polychromatic418967fa.accept_10_5_4_1_1_842 25 144 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 144 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 144 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 144 211 (accept_3_3 23 144 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 144 211 (Polychromatic418967fa.accept_15_7_9_1_1_473 22 144 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 144 211
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 144 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 144 211 (accept_3_3 20 144 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 144 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 144 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 144 211 (Polychromatic418967fa.accept_13_5_1_3_1_878 18 144 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 144 211 (accept_3_3 17 144 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 144 211 (Polychromatic418967fa.accept_17_16_8_7_1_4983 16 144
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 144 211
  (Polychromatic418967fa.accept_10_5_4_1_1_842 15 144 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 144 211 (accept_3_3 14 144 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 144 211 (Polychromatic418967fa.accept_19_13_11_2_1_4112 13 144 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 144 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 144 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 144 211 (accept_3_3 11 144 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 144 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 144 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 144 211
  (Polychromatic418967fa.accept_19_9_11_2_1_5436 9 144 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 144 211 (accept_3_3 8 144 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  144 211 (Polychromatic418967fa.accept_10_7_4_1_1_1319 7 144 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 144 211 (Polychromatic418967fa.accept_13_6_1_3_1_1522 6 144 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 144 211 (accept_3_3 5 144 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 144 211 (Polychromatic418967fa.accept_13_4_1_3_1_3058 4 144 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 144 211
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 144 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 144 211 (accept_3_3 2 144 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  144 211 (Polychromatic418967fa.accept_17_1_8_7_1_4982 1 144 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 144 211)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 143
  211 (Eq.refl Bool.true) (allA_of_3_1 69 143 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 70 142 211
  (Eq.refl Bool.true) (allA_succ_of_accept 69 142 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 142 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 142 211 (accept_3_3 68 142 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 142 211 (Polychromatic418967fa.accept_11_1_10_2_1_58 67 142
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 142 211
  (Polychromatic418967fa.accept_7_3_2_1_1_225 66 142 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 142 211 (accept_3_3 65 142 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 142 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 64 142 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 142 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 142 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 142 211 (accept_3_3 62 142 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 142 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 142 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 142 211
  (Polychromatic418967fa.accept_9_6_7_4_1_212 60 142 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 142 211 (accept_3_3 59 142 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 142 211 (Polychromatic418967fa.accept_19_1_9_2_1_6945 58 142 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 142 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 142 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 142 211 (accept_3_3 56 142 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 142 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 55 142 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 142 211
  (Polychromatic418967fa.accept_13_2_12_3_1_415 54 142 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 142 211 (accept_3_3 53 142 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 142 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 52 142 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 142 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 142 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 142 211 (accept_3_3 50 142 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 142 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 142 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 142 211
  (Polychromatic418967fa.accept_7_6_2_1_1_214 48 142 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 142 211 (accept_3_3 47 142 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 142 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 142 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 142 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 142 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 142 211 (accept_3_3 44 142 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 142 211 (Polychromatic418967fa.accept_10_3_2_1_1_839 43 142 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 142 211
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 142 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 142 211 (accept_3_3 41 142 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 142 211 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 142 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 142 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 142 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 142 211 (accept_3_3 38 142 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 142 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 142 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 142 211
  (Polychromatic418967fa.accept_10_6_2_1_1_494 36 142 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 142 211 (accept_3_3 35 142 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 142 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 142 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 142 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 142 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 142 211 (accept_3_3 32 142 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 142 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 142 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 142 211
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 142 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 142 211 (accept_3_3 29 142 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 142 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 142 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 142 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 142 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 142 211 (accept_3_3 26 142 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 142 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 142 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 142 211
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 142 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 142 211 (accept_3_3 23 142 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 142 211 (Polychromatic418967fa.accept_13_9_12_3_1_907 22 142 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 142 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 142 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 142 211 (accept_3_3 20 142 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 142 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 142 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 142 211
  (Polychromatic418967fa.accept_19_18_9_2_1_9764 18 142 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 142 211 (accept_3_3 17 142 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 142 211 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 142 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 142 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 142 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 142 211 (accept_3_3 14 142 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 142 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 142 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 142 211
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 142 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 142 211 (accept_3_3 11 142 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 142 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 142 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 142 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 142 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 142 211 (accept_3_3 8 142 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 142 211 (Polychromatic418967fa.accept_19_7_9_2_1_4090 7 142 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 142 211
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 142 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 142 211 (accept_3_3 5 142 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  142 211 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 142 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 142 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 142 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 142 211 (accept_3_3 2 142 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 142 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 142 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142
  211)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 141 211 (Eq.refl Bool.true)
  (allA_succ_of_accept 70 141 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 141 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 141 211 (Polychromatic418967fa.accept_15_9_6_1_1_493 69 141
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 141 211 (accept_3_3 68 141
  211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 141 211
  (Polychromatic418967fa.accept_13_2_11_3_1_873 67 141 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 141 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 141 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 141 211 (accept_3_3 65 141 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 141 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 141 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 141 211 (Polychromatic418967fa.accept_12_3_9_7_1_472
  63 141 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 141 211 (accept_3_3 62
  141 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 141 211
  (Polychromatic418967fa.accept_9_7_6_4_1_483 61 141 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 141 211 (Polychromatic418967fa.accept_13_8_11_3_1_3053 60 141 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 141 211 (accept_3_3 59 141 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 141 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 141 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 141 211 (Polychromatic418967fa.accept_9_3_6_4_1_210
  57 141 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 141 211 (accept_3_3 56
  141 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 141 211
  (Polychromatic418967fa.accept_9_1_6_4_1_49 55 141 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 141 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 141 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 141 211 (accept_3_3 53 141 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 141 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 141 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 141 211 (Polychromatic418967fa.accept_11_7_9_2_1_260
  51 141 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 141 211 (accept_3_3 50
  141 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 141 211
  (Polychromatic418967fa.accept_13_10_11_3_1_1518 49 141 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 141 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 48 141 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 141 211 (accept_3_3 47 141 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 141 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 141 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 141 211
  (Polychromatic418967fa.accept_17_11_5_7_1_6177 45 141 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 141 211 (accept_3_3 44 141 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 141 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 141 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 141 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 141 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 141 211 (accept_3_3 41 141 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 141 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 141 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 141 211
  (Polychromatic418967fa.accept_9_3_6_4_1_210 39 141 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 141 211 (accept_3_3 38 141 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 141 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 141 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 141 211 (Polychromatic418967fa.accept_13_10_11_3_1_1518 36 141 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 141 211 (accept_3_3 35 141 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 141 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 141 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 141 211
  (Polychromatic418967fa.accept_13_7_11_3_1_1540 33 141 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 141 211 (accept_3_3 32 141 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 141 211 (Polychromatic418967fa.accept_13_5_11_3_1_902 31 141 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 141 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 141 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 141 211 (accept_3_3 29 141 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 141 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 141 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 141 211
  (Polychromatic418967fa.accept_12_3_9_7_1_472 27 141 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 141 211 (accept_3_3 26 141 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 141 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 141 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 141 211 (Polychromatic418967fa.accept_15_9_6_1_1_493 24 141 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 141 211 (accept_3_3 23 141 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 141 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 141 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 141 211
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 141 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 141 211 (accept_3_3 20 141 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 141 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 141 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 141 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 141 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 141 211 (accept_3_3 17 141 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 141 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 141 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 141 211
  (Polychromatic418967fa.accept_11_4_9_2_1_259 15 141 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 141 211 (accept_3_3 14 141 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 141 211 (Polychromatic418967fa.accept_19_13_8_2_1_4089 13 141 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 141 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 141 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 141 211 (accept_3_3 11 141 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 141 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 141 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 141 211
  (Polychromatic418967fa.accept_15_9_6_1_1_493 9 141 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 141 211 (accept_3_3 8 141 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  141 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 141 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 141 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 141 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 141 211 (accept_3_3 5 141 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 141 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 141 211
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 141 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 141 211 (accept_3_3 2 141 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  141 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 141 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 141 211))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72
  140 211 (Eq.refl Bool.true) (allA_of_3_1 72 140 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 73 139 211
  (Eq.refl Bool.true) (allA_succ_of_accept 72 139 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 72 139 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 139 211 (accept_3_3 71 139 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 139 211 (Polychromatic418967fa.accept_13_5_9_3_1_870 70 139
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 139 211
  (Polychromatic418967fa.accept_19_12_6_2_1_5424 69 139 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 139 211 (accept_3_3 68 139 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 139 211 (Polychromatic418967fa.accept_13_2_9_3_1_2212 67 139 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 139 211 (Polychromatic418967fa.accept_23_20_1_4_1_12521 66 139 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 139 211 (accept_3_3 65 139 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 139 211 (Polychromatic418967fa.accept_11_9_7_2_1_1068 64 139
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 139 211
  (Polychromatic418967fa.accept_14_7_13_1_1_922 63 139 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 139 211 (accept_3_3 62 139 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 139 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 61 139 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 139 211 (Polychromatic418967fa.accept_13_8_9_3_1_2213 60 139 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 139 211 (accept_3_3 59 139 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 139 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 58 139 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 139 211
  (Polychromatic418967fa.accept_13_5_9_3_1_870 57 139 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 139 211 (accept_3_3 56 139 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 139 211 (Polychromatic418967fa.accept_10_5_9_1_1_187 55 139 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 139 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 54 139 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 139 211 (accept_3_3 53 139 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 139 211 (Polychromatic418967fa.accept_10_2_9_1_1_185 52 139 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 139 211
  (Polychromatic418967fa.accept_7_2_6_1_1_73 51 139 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 139 211 (accept_3_3 50 139 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 139 211 (Polychromatic418967fa.accept_14_7_13_1_1_922 49 139 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 139 211 (Polychromatic418967fa.accept_10_8_9_1_1_189 48 139 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 139 211 (accept_3_3 47 139 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 139 211 (Polychromatic418967fa.accept_13_7_9_3_1_1504 46 139
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 139 211
  (Polychromatic418967fa.accept_10_5_9_1_1_187 45 139 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 139 211 (accept_3_3 44 139 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 139 211 (Polychromatic418967fa.accept_22_21_7_13_1_10883 43 139 211 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 139 211 (Polychromatic418967fa.accept_10_2_9_1_1_185 42 139 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 139 211 (accept_3_3 41 139 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 139 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 139 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 139 211
  (Polychromatic418967fa.accept_16_7_11_3_1_1330 39 139 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 139 211 (accept_3_3 38 139 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 139 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 139 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 139 211 (Polychromatic418967fa.accept_27_9_4_22_1_12520 36 139 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 139 211 (accept_3_3 35 139 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 139 211 (Polychromatic418967fa.accept_13_8_9_3_1_2213 34 139
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 139 211
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 139 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 139 211 (accept_3_3 32 139 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 139 211 (Polychromatic418967fa.accept_11_9_7_2_1_1068 31 139 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 139 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 139 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 139 211 (accept_3_3 29 139 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 139 211 (Polychromatic418967fa.accept_10_8_9_1_1_189 28 139 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 139 211
  (Polychromatic418967fa.accept_15_12_4_1_1_3746 27 139 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 139 211 (accept_3_3 26 139 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 139 211 (Polychromatic418967fa.accept_10_5_9_1_1_187 25 139 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 139 211 (Polychromatic418967fa.accept_16_8_11_3_1_4279 24 139 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 139 211 (accept_3_3 23 139 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 139 211 (Polychromatic418967fa.accept_10_2_9_1_1_185 22 139
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 139 211
  (Polychromatic418967fa.accept_13_8_9_3_1_2213 21 139 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 139 211 (accept_3_3 20 139 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 139 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 139 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 139 211 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 139 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 139 211 (accept_3_3 17 139 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 139 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 139 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 139 211
  (Polychromatic418967fa.accept_10_5_9_1_1_187 15 139 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 139 211 (accept_3_3 14 139 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 139 211 (Polychromatic418967fa.accept_19_13_6_2_1_4124 13 139 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 139 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 139 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 139 211 (accept_3_3 11 139 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 139 211 (Polychromatic418967fa.accept_17_10_3_7_1_1679 10 139 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 139 211
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 139 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 139 211 (accept_3_3 8 139 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  139 211 (Polychromatic418967fa.accept_13_7_9_3_1_1504 7 139 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 139 211 (Polychromatic418967fa.accept_13_6_9_3_1_915 6 139 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 139 211 (accept_3_3 5 139 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 139 211 (Polychromatic418967fa.accept_17_4_3_7_1_4971 4 139 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 139 211
  (Polychromatic418967fa.accept_15_3_4_1_1_1072 3 139 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 139 211 (accept_3_3 2 139 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  139 211 (Polychromatic418967fa.accept_19_1_6_2_1_8341 1 139 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 139 211))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74
  138 211 (Eq.refl Bool.true) (allA_succ_of_accept 73 138 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 138 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 138 211
  (Polychromatic418967fa.accept_13_7_8_3_1_1533 72 138 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 138 211 (accept_3_3 71 138 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 138 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 70 138 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 138 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 138 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 138 211 (accept_3_3 68 138 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 138 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 67 138 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 138 211
  (Polychromatic418967fa.accept_7_3_5_1_1_72 66 138 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 138 211 (accept_3_3 65 138 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 138 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 64 138 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 138 211 (Polychromatic418967fa.accept_10_3_8_1_1_182 63 138 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 138 211 (accept_3_3 62 138 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 138 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 138 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 138 211
  (Polychromatic418967fa.accept_7_4_5_1_1_418 60 138 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 138 211 (accept_3_3 59 138 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 138 211 (Polychromatic418967fa.accept_15_13_3_1_1_3740 58 138 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 138 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 138 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 138 211 (accept_3_3 56 138 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 138 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 55 138 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 138 211
  (Polychromatic418967fa.accept_19_16_5_2_1_8375 54 138 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 138 211 (accept_3_3 53 138 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 138 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 52 138 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 138 211 (Polychromatic418967fa.accept_9_6_3_4_1_477 51 138 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 138 211 (accept_3_3 50 138 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 138 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 138 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 138 211
  (Polychromatic418967fa.accept_7_6_5_1_1_416 48 138 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 138 211 (accept_3_3 47 138 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 138 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 46 138 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 138 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 138 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 138 211 (accept_3_3 44 138 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 138 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 138 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 138 211
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 138 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 138 211 (accept_3_3 41 138 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 138 211 (Polychromatic418967fa.accept_21_19_12_1_1_11027 40 138 211 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 138 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 138 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 138 211 (accept_3_3 38 138 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 138 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 138 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 138 211
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 36 138 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 138 211 (accept_3_3 35 138 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 138 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 138 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 138 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 138 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 138 211 (accept_3_3 32 138 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 138 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 138 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 138 211
  (Polychromatic418967fa.accept_17_13_2_7_1_6122 30 138 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 138 211 (accept_3_3 29 138 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 138 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 138 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 138 211 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 138 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 138 211 (accept_3_3 26 138 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 138 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 138 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 138 211
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 138 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 138 211 (accept_3_3 23 138 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 138 211 (Polychromatic418967fa.accept_13_9_8_3_1_3045 22 138 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 138 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 138 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 138 211 (accept_3_3 20 138 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 138 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 138 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 138 211
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 138 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 138 211 (accept_3_3 17 138 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 138 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 138 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 138 211 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 138 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 138 211 (accept_3_3 14 138 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 138 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 138 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 138 211
  (Polychromatic418967fa.accept_16_12_10_3_1_4209 12 138 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 138 211 (accept_3_3 11 138 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 138 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 138 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 138 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 138 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 138 211 (accept_3_3 8 138 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 138 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 7
  138 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 138 211
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 138 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 138 211 (accept_3_3 5 138 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  138 211 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 138 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 138 211 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 138 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 138 211 (accept_3_3 2 138 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 138 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 138 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  211)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 137 211 (Eq.refl
  Bool.true) (allA_of_3_1 75 137 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 76 136 211 (Eq.refl Bool.true)
  (allA_succ_of_accept 75 136 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 136 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 136 211 (accept_3_3 74 136 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 136 211 (Polychromatic418967fa.accept_18_1_10_13_1_500 73 136 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 136 211
  (Polychromatic418967fa.accept_7_2_3_1_1_10 72 136 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 136 211 (accept_3_3 71 136 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 136 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 136 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 136 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 136 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 136 211 (accept_3_3 68 136 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 136 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 67 136 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 136 211
  (Polychromatic418967fa.accept_9_3_1_4_1_216 66 136 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 136 211 (accept_3_3 65 136 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 136 211 (Polychromatic418967fa.accept_11_9_4_2_1_600 64 136 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 136 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 136 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 136 211 (accept_3_3 62 136 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 136 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 61 136 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 136 211
  (Polychromatic418967fa.accept_7_4_3_1_1_87 60 136 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 136 211 (accept_3_3 59 136 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 136 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 58 136 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 136 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 136 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 136 211 (accept_3_3 56 136 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 136 211 (Polychromatic418967fa.accept_10_5_6_1_1_836 55 136 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 136 211
  (Polychromatic418967fa.accept_7_5_3_1_1_424 54 136 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 136 211 (accept_3_3 53 136 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 136 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 136 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 136 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 136 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 136 211 (accept_3_3 50 136 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 136 211 (Polychromatic418967fa.accept_13_10_6_3_1_1515 49 136 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 136 211
  (Polychromatic418967fa.accept_9_3_1_4_1_216 48 136 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 136 211 (accept_3_3 47 136 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 136 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 46 136 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 136 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 136 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 136 211 (accept_3_3 44 136 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 136 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 136 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 136 211
  (Polychromatic418967fa.accept_9_6_1_4_1_474 42 136 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 136 211 (accept_3_3 41 136 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 136 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 136 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 136 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 136 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 136 211 (accept_3_3 38 136 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 136 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 136 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 136 211
  (Polychromatic418967fa.accept_13_10_6_3_1_1515 36 136 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 136 211 (accept_3_3 35 136 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 136 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 136 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 136 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 136 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 136 211 (accept_3_3 32 136 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 136 211 (Polychromatic418967fa.accept_11_9_4_2_1_600 31 136 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 136 211
  (Polychromatic418967fa.accept_7_2_3_1_1_10 30 136 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 136 211 (accept_3_3 29 136 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 136 211 (Polychromatic418967fa.accept_11_6_4_2_1_599 28 136 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 136 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 136 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 136 211 (accept_3_3 26 136 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 136 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 136 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 136 211
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 136 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 136 211 (accept_3_3 23 136 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 136 211 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 136 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 136 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 136 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 136 211 (accept_3_3 20 136 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 136 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 136 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 136 211
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 136 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 136 211 (accept_3_3 17 136 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 136 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 136 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 136 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 136 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 136 211 (accept_3_3 14 136 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 136 211 (Polychromatic418967fa.accept_16_13_8_3_1_5374 13 136 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 136 211
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 136 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 136 211 (accept_3_3 11 136 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 136 211 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 136 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 136 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 136 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 136 211 (accept_3_3 8 136 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 136 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 136 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 136 211
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 136 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 136 211 (accept_3_3 5 136 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  136 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 136 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 136 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 136 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 136 211 (accept_3_3 2 136 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 136 211 (Polychromatic418967fa.accept_13_1_6_3_1_1547 1 136 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 136
  211)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 135 211 (Eq.refl
  Bool.true) (allA_succ_of_accept 76 135 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 135 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 135 211
  (Polychromatic418967fa.accept_16_11_7_3_1_3163 75 135 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 135 211 (accept_3_3 74 135 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 135 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 73 135 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 135 211 (Polychromatic418967fa.accept_25_22_10_11_1_12519 72 135 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 135 211 (accept_3_3 71 135 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 135 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 135 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 135 211
  (Polychromatic418967fa.accept_7_6_2_1_1_214 69 135 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 135 211 (accept_3_3 68 135 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 135 211 (Polychromatic418967fa.accept_11_1_3_2_1_1090 67 135 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 135 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 66 135 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 135 211 (accept_3_3 65 135 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 135 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 135 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 135 211
  (Polychromatic418967fa.accept_13_11_5_3_1_889 63 135 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 135 211 (accept_3_3 62 135 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 135 211 (Polychromatic418967fa.accept_13_9_5_3_1_428 61 135 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 135 211 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 135 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 135 211 (accept_3_3 59 135 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 135 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 135 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 135 211
  (Polychromatic418967fa.accept_12_9_3_7_1_924 57 135 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 135 211 (accept_3_3 56 135 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 135 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 55 135 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 135 211 (Polychromatic418967fa.accept_10_4_5_1_1_497 54 135 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 135 211 (accept_3_3 53 135 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 135 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 135 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 135 211
  (Polychromatic418967fa.accept_25_1_10_11_1_12518 51 135 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 135 211 (accept_3_3 50 135 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 135 211 (Polychromatic418967fa.accept_10_9_5_1_1_1325 49 135 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 135 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 135 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 135 211 (accept_3_3 47 135 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 135 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 46
  135 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 135 211
  (Polychromatic418967fa.accept_7_3_2_1_1_225 45 135 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 135 211 (accept_3_3 44 135 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 135 211 (Polychromatic418967fa.accept_16_11_7_3_1_3163 43 135 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 135 211 (Polychromatic418967fa.accept_16_10_7_3_1_6601 42 135 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 135 211 (accept_3_3 41 135 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 135 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 135 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 135 211
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 39 135 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 135 211 (accept_3_3 38 135 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 135 211 (Polychromatic418967fa.accept_13_11_5_3_1_889 37 135 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 135 211 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 135 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 135 211 (accept_3_3 35 135 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 135 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 135 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 135 211
  (Polychromatic418967fa.accept_12_9_3_7_1_924 33 135 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 135 211 (accept_3_3 32 135 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 135 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 135 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 135 211 (Polychromatic418967fa.accept_20_10_15_11_1_3759 30 135 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 135 211 (accept_3_3 29 135 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 135 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 135 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 135 211
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 135 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 135 211 (accept_3_3 26 135 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 135 211 (Polychromatic418967fa.accept_16_9_7_3_1_614 25 135 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 135 211 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 135 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 135 211 (accept_3_3 23 135 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 135 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 135 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 135 211
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 135 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 135 211 (accept_3_3 20 135 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 135 211 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 135 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 135 211 (Polychromatic418967fa.accept_21_18_9_1_1_9467 18 135 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 135 211 (accept_3_3 17 135 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 135 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 135 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 135 211
  (Polychromatic418967fa.accept_13_2_5_3_1_406 15 135 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 135 211 (accept_3_3 14 135 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 135 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 135 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 135 211 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 135 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 135 211 (accept_3_3 11 135 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 135 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 135 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 135 211
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 135 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 135 211 (accept_3_3 8 135 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  135 211 (Polychromatic418967fa.accept_23_7_20_4_1_12517 7 135 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 135 211 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 135 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 135 211 (accept_3_3 5 135 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 135 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 135 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 135 211
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 135 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 135 211 (accept_3_3 2 135 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  135 211 (Polychromatic418967fa.accept_11_1_3_2_1_1090 1 135 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 135 211))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  78 134 211 (Eq.refl Bool.true) (allA_of_3_1 78 134 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 79 133 211
  (Eq.refl Bool.true) (allA_succ_of_accept 78 133 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 133 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 133 211 (accept_3_3 77 133 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 133 211 (Polychromatic418967fa.accept_11_10_1_2_1_1624 76 133
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 133 211
  (Polychromatic418967fa.accept_9_3_7_4_1_53 75 133 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 133 211 (accept_3_3 74 133 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 133 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 73 133 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 133 211 (Polychromatic418967fa.accept_10_2_3_1_1_481 72 133 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 133 211 (accept_3_3 71 133 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 133 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 133 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 133 211
  (Polychromatic418967fa.accept_9_6_7_4_1_212 69 133 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 133 211 (accept_3_3 68 133 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 133 211 (Polychromatic418967fa.accept_21_4_7_1_1_6307 67 133 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 133 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 133 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 133 211 (accept_3_3 65 133 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 133 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 64 133 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 133 211
  (Polychromatic418967fa.accept_15_3_13_1_1_479 63 133 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 133 211 (accept_3_3 62 133 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 133 211 (Polychromatic418967fa.accept_17_10_14_7_1_2679 61 133 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 133 211 (Polychromatic418967fa.accept_9_6_7_4_1_212 60 133 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 133 211 (accept_3_3 59 133 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 133 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 133 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 133 211
  (Polychromatic418967fa.accept_9_3_7_4_1_53 57 133 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 133 211 (accept_3_3 56 133 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 133 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 133 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 133 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 133 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 133 211 (accept_3_3 53 133 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 133 211 (Polychromatic418967fa.accept_10_2_3_1_1_481 52 133 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 133 211
  (Polychromatic418967fa.accept_9_6_7_4_1_212 51 133 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 133 211 (accept_3_3 50 133 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 133 211 (Polychromatic418967fa.accept_24_1_13_19_1_2191 49 133 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 133 211 (Polychromatic418967fa.accept_9_3_7_4_1_53 48 133 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 133 211 (accept_3_3 47 133 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 133 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 133 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 133 211
  (Polychromatic418967fa.accept_21_3_7_1_1_9521 45 133 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 133 211 (accept_3_3 44 133 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 133 211 (Polychromatic418967fa.accept_11_10_1_2_1_1624 43 133 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 133 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 133 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 133 211 (accept_3_3 41 133 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 133 211 (Polychromatic418967fa.accept_15_10_13_1_1_3698 40 133 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 133 211
  (Polychromatic418967fa.accept_9_3_7_4_1_53 39 133 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 133 211 (accept_3_3 38 133 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 133 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 133 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 133 211 (Polychromatic418967fa.accept_11_3_1_2_1_1063 36 133 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 133 211 (accept_3_3 35 133 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 133 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 133 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 133 211
  (Polychromatic418967fa.accept_9_6_7_4_1_212 33 133 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 133 211 (accept_3_3 32 133 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 133 211 (Polychromatic418967fa.accept_21_10_7_1_1_9464 31 133 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 133 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 133 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 133 211 (accept_3_3 29 133 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 133 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 133 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 133 211
  (Polychromatic418967fa.accept_14_13_7_1_1_1618 27 133 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 133 211 (accept_3_3 26 133 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 133 211 (Polychromatic418967fa.accept_11_3_1_2_1_1063 25 133 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 133 211 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 133 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 133 211 (accept_3_3 23 133 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 133 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 133 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 133 211
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 133 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 133 211 (accept_3_3 20 133 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 133 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 133 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 133 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 133 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 133 211 (accept_3_3 17 133 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 133 211 (Polychromatic418967fa.accept_21_16_7_1_1_9430 16 133 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 133 211
  (Polychromatic418967fa.accept_9_6_7_4_1_212 15 133 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 133 211 (accept_3_3 14 133 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 133 211 (Polychromatic418967fa.accept_14_13_7_1_1_1618 13 133 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 133 211 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 133 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 133 211 (accept_3_3 11 133 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 133 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 133 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 133 211
  (Polychromatic418967fa.accept_22_9_1_13_1_7731 9 133 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 133 211 (accept_3_3 8 133 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  133 211 (Polychromatic418967fa.accept_24_7_13_19_1_12516 7 133 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 133 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 133 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 133 211 (accept_3_3 5 133 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 133 211 (Polychromatic418967fa.accept_17_4_14_7_1_4965 4 133 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 133 211
  (Polychromatic418967fa.accept_9_3_7_4_1_53 3 133 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 133 211 (accept_3_3 2 133 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  133 211 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 133 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 133 211)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 80 132 211 (Eq.refl Bool.true) (allA_succ_of_accept 79 132 211 (Polychromatic418967fa.accept_7_2_6_1_1_73
  79 132 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 132 211
  (Polychromatic418967fa.accept_21_15_6_1_1_6306 78 132 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 132 211 (accept_3_3 77 132 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 132 211 (Polychromatic418967fa.accept_10_6_2_1_1_494 76 132 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 132 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 75 132 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 132 211 (accept_3_3 74 132 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 132 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 73 132 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 132 211
  (Polychromatic418967fa.accept_7_2_6_1_1_73 72 132 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 132 211 (accept_3_3 71 132 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 132 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 70 132 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 132 211 (Polychromatic418967fa.accept_10_9_2_1_1_840 69 132 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 132 211 (accept_3_3 68 132 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 132 211 (Polychromatic418967fa.accept_19_10_18_2_1_6936 67 132
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 132 211
  (Polychromatic418967fa.accept_9_3_6_4_1_210 66 132 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 132 211 (accept_3_3 65 132 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 132 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 64 132 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 132 211 (Polychromatic418967fa.accept_8_7_4_3_1_156 63 132 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 132 211 (accept_3_3 62 132 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 132 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 61 132 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 132 211
  (Polychromatic418967fa.accept_16_12_4_3_1_4295 60 132 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 132 211 (accept_3_3 59 132 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 132 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 58 132 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 132 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 57 132 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 132 211 (accept_3_3 56 132 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 132 211 (Polychromatic418967fa.accept_8_7_4_3_1_156 55 132 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 132 211
  (Polychromatic418967fa.accept_7_5_6_1_1_407 54 132 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 132 211 (accept_3_3 53 132 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 132 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 52 132 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 132 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 132 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 132 211 (accept_3_3 50 132 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 132 211 (Polychromatic418967fa.accept_10_9_2_1_1_840 49 132 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 132 211
  (Polychromatic418967fa.accept_9_3_6_4_1_210 48 132 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 132 211 (accept_3_3 47 132 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 132 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 46 132 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 132 211 (Polychromatic418967fa.accept_17_11_13_7_1_3795 45 132 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 132 211 (accept_3_3 44 132 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 132 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 132 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 132 211
  (Polychromatic418967fa.accept_19_4_18_2_1_9779 42 132 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 132 211 (accept_3_3 41 132 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 132 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 132 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 132 211 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 132 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 132 211 (accept_3_3 38 132 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 132 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 132 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 132 211
  (Polychromatic418967fa.accept_10_6_2_1_1_494 36 132 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 132 211 (accept_3_3 35 132 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 132 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 132 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 132 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 132 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 132 211 (accept_3_3 32 132 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 132 211 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 132 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 132 211
  (Polychromatic418967fa.accept_7_2_6_1_1_73 30 132 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 132 211 (accept_3_3 29 132 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 132 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 132 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 132 211 (Polychromatic418967fa.accept_13_1_2_3_1_911 27 132 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 132 211 (accept_3_3 26 132 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 132 211 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 132 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 132 211
  (Polychromatic418967fa.accept_13_11_2_3_1_883 24 132 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 132 211 (accept_3_3 23 132 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 132 211 (Polychromatic418967fa.accept_13_9_2_3_1_3027 22 132 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 132 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 132 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 132 211 (accept_3_3 20 132 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 132 211 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 132 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 132 211
  (Polychromatic418967fa.accept_13_5_2_3_1_1526 18 132 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 132 211 (accept_3_3 17 132 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 132 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 132 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 132 211 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 132 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 132 211 (accept_3_3 14 132 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 132 211 (Polychromatic418967fa.accept_10_3_2_1_1_839 13 132 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 132 211
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 132 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 132 211 (accept_3_3 11 132 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 132 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 132 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 132 211 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 132 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 132 211 (accept_3_3 8 132 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 132 211 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 132 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 132 211
  (Polychromatic418967fa.accept_10_6_2_1_1_494 6 132 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 132 211 (accept_3_3 5 132 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  132 211 (Polychromatic418967fa.accept_15_4_12_1_1_1081 4 132 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 132 211 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 132 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 132 211 (accept_3_3 2 132 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 132 211 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 132 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132
  211)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 81 131 211 (Eq.refl
  Bool.true) (allA_of_3_1 81 131 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 82 130 211 (Eq.refl Bool.true)
  (allA_succ_of_accept 81 130 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 130 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 130 211 (accept_3_3 80 130 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 130 211 (Polychromatic418967fa.accept_16_15_2_3_1_4262 79 130 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 130 211
  (Polychromatic418967fa.accept_29_20_14_8_1_12515 78 130 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 130 211 (accept_3_3 77 130 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 130 211 (Polychromatic418967fa.accept_12_4_10_7_1_149 76 130 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 130 211 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 130 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 130 211 (accept_3_3 74 130 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 130 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 73
  130 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 130 211
  (Polychromatic418967fa.accept_22_6_20_13_1_10914 72 130 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 130 211 (accept_3_3 71 130 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 130 211 (Polychromatic418967fa.accept_11_4_9_2_1_259 70 130 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 130 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 130 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 130 211 (accept_3_3 68 130 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 130 211
  (Polychromatic418967fa.accept_14_11_4_1_1_4255 67 130 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 130 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 66 130 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 130 211 (accept_3_3 65 130 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 130 211 (Polychromatic418967fa.accept_12_4_10_7_1_149 64 130 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 130 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 130 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 130 211 (accept_3_3 62 130 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 130 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 130 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 130 211 (Polychromatic418967fa.accept_19_3_16_2_1_6837 60 130 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 130 211 (accept_3_3 59 130 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 130 211 (Polychromatic418967fa.accept_15_13_10_1_1_1862 58 130
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 130 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 130 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 130 211 (accept_3_3 56 130 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 130 211 (Polychromatic418967fa.accept_19_17_16_2_1_8390 55 130 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 130 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 130 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 130 211 (accept_3_3 53 130 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 130 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 130 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 130 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 130 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 130 211 (accept_3_3 50 130 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 130 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 130 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 130 211 (Polychromatic418967fa.accept_11_4_9_2_1_259 48 130 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 130 211 (accept_3_3 47 130 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 130 211 (Polychromatic418967fa.accept_18_10_4_13_1_3296 46 130
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 130 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 130 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 130 211 (accept_3_3 44 130 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 130 211 (Polychromatic418967fa.accept_15_13_10_1_1_1862 43 130 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 130 211 (Polychromatic418967fa.accept_19_4_16_2_1_6967 42 130 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 130 211 (accept_3_3 41 130 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 130 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 40 130 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 130 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 130 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 130 211 (accept_3_3 38 130 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 130 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 130 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 130 211 (Polychromatic418967fa.accept_15_6_10_1_1_3675 36 130 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 130 211 (accept_3_3 35 130 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 130 211 (Polychromatic418967fa.accept_20_14_10_11_1_2393 34
  130 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 130 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 130 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 130 211 (accept_3_3 32 130 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 130 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 130 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 130 211 (Polychromatic418967fa.accept_17_13_11_7_1_4961 30 130 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 130 211 (accept_3_3 29 130 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 130 211 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 130
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 130 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 130 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 130 211 (accept_3_3 26 130 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 130 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 130 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 130 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 130 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 130 211 (accept_3_3 23 130 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 130 211 (Polychromatic418967fa.accept_15_7_10_1_1_1836 22 130 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 130 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 130 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 130 211 (accept_3_3 20 130 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 130 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 130 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 130 211 (Polychromatic418967fa.accept_11_7_9_2_1_260 18 130 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 130 211 (accept_3_3 17 130 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 130 211 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 130
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 130 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 130 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 130 211 (accept_3_3 14 130 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 130 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 130 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 130 211 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 130 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 130 211 (accept_3_3 11 130 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 130 211 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 130 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 130 211
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 130 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 130 211 (accept_3_3 8 130 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  130 211 (Polychromatic418967fa.accept_11_7_9_2_1_260 7 130 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 130 211 (Polychromatic418967fa.accept_15_6_10_1_1_3675 6 130 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 130 211 (accept_3_3 5 130 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 130 211 (Polychromatic418967fa.accept_11_4_9_2_1_259 4 130 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 130 211
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 130 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 130 211 (accept_3_3 2 130 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  130 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 130 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 130 211))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 83 129 211 (Eq.refl Bool.true) (allA_succ_of_accept 82 129 211 (Polychromatic418967fa.accept_4_2_1_3_1_27
  82 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 129 211
  (Polychromatic418967fa.accept_7_4_3_1_1_87 81 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 129 211 (accept_3_3 80 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 129 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 79 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 129 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 129 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 129 211 (accept_3_3 77 129 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 129 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 129 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 129 211
  (Polychromatic418967fa.accept_7_5_3_1_1_424 75 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 129 211 (accept_3_3 74 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 129 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 73 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 129 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 72 129 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 129 211 (accept_3_3 71 129 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 129 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 129 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 129 211
  (Polychromatic418967fa.accept_9_6_3_4_1_477 69 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 129 211 (accept_3_3 68 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 129 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 67 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 129 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 129 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 129 211 (accept_3_3 65 129 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 129 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 129 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 129 211
  (Polychromatic418967fa.accept_12_3_9_7_1_472 63 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 129 211 (accept_3_3 62 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 129 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 61 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 129 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 129 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 129 211 (accept_3_3 59 129 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 129 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 129 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 129 211
  (Polychromatic418967fa.accept_21_15_3_1_1_6338 57 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 129 211 (accept_3_3 56 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 129 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 55 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 129 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 129 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 129 211 (accept_3_3 53 129 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 129 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 129 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 129 211
  (Polychromatic418967fa.accept_7_2_3_1_1_10 51 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 129 211 (accept_3_3 50 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 129 211 (Polychromatic418967fa.accept_11_5_8_2_1_588 49 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 129 211 (Polychromatic418967fa.accept_10_8_9_1_1_189 48 129 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 129 211 (accept_3_3 47 129 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 129 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 129 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 129 211
  (Polychromatic418967fa.accept_10_5_9_1_1_187 45 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 129 211 (accept_3_3 44 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 129 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 129 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 129 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 129 211 (accept_3_3 41 129 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 129 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 129 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 129 211
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 129 211 (accept_3_3 38 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 129 211 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 129 211 (Polychromatic418967fa.accept_15_6_9_1_1_1823 36 129 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 129 211 (accept_3_3 35 129 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 129 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 129 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 129 211
  (Polychromatic418967fa.accept_7_5_3_1_1_424 33 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 129 211 (accept_3_3 32 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 129 211 (Polychromatic418967fa.accept_17_14_10_7_1_2670 31 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 129 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 129 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 129 211 (accept_3_3 29 129 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 129 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 129 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 129 211
  (Polychromatic418967fa.accept_11_5_8_2_1_588 27 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 129 211 (accept_3_3 26 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 129 211 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 129 211 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 129 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 129 211 (accept_3_3 23 129 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 129 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 129 211
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 21 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 129 211 (accept_3_3 20 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 129 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 129 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 129 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 129 211 (accept_3_3 17 129 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 129 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 129 211
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 129 211 (accept_3_3 14 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 129 211 (Polychromatic418967fa.accept_16_13_1_3_1_2205 13 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 129 211 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 129 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 129 211 (accept_3_3 11 129 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 129 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 129 211
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 129 211 (accept_3_3 8 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  129 211 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 129 211 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 129 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 129 211 (accept_3_3 5 129 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 211 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 129 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 129 211
  (Polychromatic418967fa.accept_12_3_9_7_1_472 3 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 129 211 (accept_3_3 2 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  129 211 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 129 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 129 211)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 84 128 211 (Eq.refl Bool.true) (allA_of_3_1 84 128 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 85 127 211 (Eq.refl Bool.true) (allA_succ_of_accept 84 127 211 (Polychromatic418967fa.accept_8_4_7_3_1_144
  84 127 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 127 211 (accept_3_3 83
  127 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 127 211
  (Polychromatic418967fa.accept_16_2_15_3_1_1300 82 127 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 127 211 (Polychromatic418967fa.accept_11_4_6_2_1_51 81 127 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 127 211 (accept_3_3 80 127 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 127 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 79 127 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 127 211 (Polychromatic418967fa.accept_9_6_1_4_1_474
  78 127 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 127 211 (accept_3_3 77
  127 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 127 211
  (Polychromatic418967fa.accept_8_4_7_3_1_144 76 127 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 127 211 (Polychromatic418967fa.accept_9_3_1_4_1_216 75 127 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 127 211 (accept_3_3 74 127 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 127 211 (Polychromatic418967fa.accept_19_16_13_2_1_6920 73 127 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 127 211
  (Polychromatic418967fa.accept_13_7_10_3_1_1505 72 127 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 127 211 (accept_3_3 71 127 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 127 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 127 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 127 211 (Polychromatic418967fa.accept_9_6_1_4_1_474 69 127 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 127 211 (accept_3_3 68 127 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 127 211 (Polychromatic418967fa.accept_13_2_10_3_1_1538 67 127 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 127 211
  (Polychromatic418967fa.accept_9_3_1_4_1_216 66 127 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 127 211 (accept_3_3 65 127 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 127 211 (Polychromatic418967fa.accept_10_4_7_1_1_471 64 127 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 127 211 (Polychromatic418967fa.accept_13_11_10_3_1_3020 63 127 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 127 211 (accept_3_3 62 127 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 127 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 127 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 127 211
  (Polychromatic418967fa.accept_8_4_7_3_1_144 60 127 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 127 211 (accept_3_3 59 127 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 127 211 (Polychromatic418967fa.accept_13_6_10_3_1_897 58 127 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 127 211 (Polychromatic418967fa.accept_9_3_1_4_1_216 57 127 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 127 211 (accept_3_3 56 127 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 127 211 (Polychromatic418967fa.accept_15_10_7_1_1_3686 55 127 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 127 211
  (Polychromatic418967fa.accept_10_4_7_1_1_471 54 127 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 127 211 (accept_3_3 53 127 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 127 211 (Polychromatic418967fa.accept_8_4_7_3_1_144 52 127 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 127 211 (Polychromatic418967fa.accept_9_6_1_4_1_474 51 127 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 127 211 (accept_3_3 50 127 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 127 211 (Polychromatic418967fa.accept_19_11_13_2_1_9770 49 127 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 127 211
  (Polychromatic418967fa.accept_9_3_1_4_1_216 48 127 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 127 211 (accept_3_3 47 127 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 127 211 (Polychromatic418967fa.accept_10_6_7_1_1_1297 46 127 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 127 211 (Polychromatic418967fa.accept_13_6_10_3_1_897 45 127 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 127 211 (accept_3_3 44 127 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 127 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 127 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 127 211
  (Polychromatic418967fa.accept_9_6_1_4_1_474 42 127 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 127 211 (accept_3_3 41 127 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 127 211 (Polychromatic418967fa.accept_15_10_7_1_1_3686 40 127 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 127 211 (Polychromatic418967fa.accept_9_3_1_4_1_216 39 127 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 127 211 (accept_3_3 38 127 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 127 211 (Polychromatic418967fa.accept_11_4_6_2_1_51 37 127 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 127 211
  (Polychromatic418967fa.accept_8_4_7_3_1_144 36 127 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 127 211 (accept_3_3 35 127 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 127 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 127 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 127 211 (Polychromatic418967fa.accept_9_6_1_4_1_474 33 127 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 127 211 (accept_3_3 32 127 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 127 211 (Polychromatic418967fa.accept_17_14_8_7_1_6183 31 127 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 127 211
  (Polychromatic418967fa.accept_9_3_1_4_1_216 30 127 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 127 211 (accept_3_3 29 127 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 127 211 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 127 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 127 211 (Polychromatic418967fa.accept_16_11_15_3_1_1304 27 127 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 127 211 (accept_3_3 26 127 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 127 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 127 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 127 211
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 127 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 127 211 (accept_3_3 23 127 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 127 211 (Polychromatic418967fa.accept_24_22_7_19_1_12514 22 127 211 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 127 211 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 127 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 127 211 (accept_3_3 20 127 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 127 211 (Polychromatic418967fa.accept_13_6_10_3_1_897 19 127
  211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 127 211
  (Polychromatic418967fa.accept_16_2_15_3_1_1300 18 127 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 127 211 (accept_3_3 17 127 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 127 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 127 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 127 211 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 127 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 127 211 (accept_3_3 14 127 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 127 211 (Polychromatic418967fa.accept_16_13_15_3_1_4196 13 127 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 127 211
  (Polychromatic418967fa.accept_8_4_7_3_1_144 12 127 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 127 211 (accept_3_3 11 127 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 127 211 (Polychromatic418967fa.accept_15_10_7_1_1_3686 10 127 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 127 211 (Polychromatic418967fa.accept_15_9_7_1_1_1075 9 127 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 127 211 (accept_3_3 8 127 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 127 211 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 127 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 127 211
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 127 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 127 211 (accept_3_3 5 127 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  127 211 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 127 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 127 211 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 127 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 127 211 (accept_3_3 2 127 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 127 211 (Polychromatic418967fa.accept_17_1_8_7_1_4982 1 127 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 127
  211))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 126 211
  (Eq.refl Bool.true) (allA_succ_of_accept 85 126 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 126 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 126 211
  (Polychromatic418967fa.accept_13_6_9_3_1_915 84 126 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 126 211 (accept_3_3 83 126 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 126 211 (Polychromatic418967fa.accept_10_2_6_1_1_1296 82 126 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 126 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 126 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 126 211 (accept_3_3 80 126 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 126 211 (Polychromatic418967fa.accept_19_3_12_2_1_9788 79 126 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 126 211
  (Polychromatic418967fa.accept_15_3_6_1_1_1834 78 126 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 126 211 (accept_3_3 77 126 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 126 211 (Polychromatic418967fa.accept_20_16_6_11_1_9657 76 126 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 126 211 (Polychromatic418967fa.accept_10_5_6_1_1_836 75 126 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 126 211 (accept_3_3 74 126 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 126 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 126 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 126 211
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 72 126 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 126 211 (accept_3_3 71 126 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 126 211 (Polychromatic418967fa.accept_13_5_9_3_1_870 70 126 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 126 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 126 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 126 211 (accept_3_3 68 126 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 126 211 (Polychromatic418967fa.accept_10_7_6_1_1_486 67 126 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 126 211
  (Polychromatic418967fa.accept_19_9_12_2_1_9776 66 126 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 126 211 (accept_3_3 65 126 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 126 211 (Polychromatic418967fa.accept_13_12_9_3_1_3047 64 126 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 126 211 (Polychromatic418967fa.accept_11_8_5_2_1_1629 63 126 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 126 211 (accept_3_3 62 126 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 126 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 126 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 126 211
  (Polychromatic418967fa.accept_13_8_9_3_1_2213 60 126 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 126 211 (accept_3_3 59 126 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 126 211 (Polychromatic418967fa.accept_13_6_9_3_1_915 58 126 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 126 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 126 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 126 211 (accept_3_3 56 126 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 126 211 (Polychromatic418967fa.accept_10_5_6_1_1_836 55 126 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 126 211
  (Polychromatic418967fa.accept_13_2_9_3_1_2212 54 126 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 126 211 (accept_3_3 53 126 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 126 211 (Polychromatic418967fa.accept_10_2_6_1_1_1296 52 126 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 126 211 (Polychromatic418967fa.accept_13_12_9_3_1_3047 51 126 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 126 211 (accept_3_3 50 126 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 126 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 126 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 126 211
  (Polychromatic418967fa.accept_15_3_6_1_1_1834 48 126 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 126 211 (accept_3_3 47 126 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 126 211 (Polychromatic418967fa.accept_13_7_9_3_1_1504 46 126 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 126 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 126 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 126 211 (accept_3_3 44 126 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 126 211 (Polychromatic418967fa.accept_16_11_14_3_1_3140 43 126 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 126 211
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 126 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 126 211 (accept_3_3 41 126 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 126 211 (Polychromatic418967fa.accept_15_10_6_1_1_3707 40 126 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 126 211 (Polychromatic418967fa.accept_15_9_6_1_1_493 39 126 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 126 211 (accept_3_3 38 126 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 126 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 126 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 126 211
  (Polychromatic418967fa.accept_19_17_12_2_1_6880 36 126 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 126 211 (accept_3_3 35 126 211 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 126 211 (Polychromatic418967fa.accept_13_8_9_3_1_2213 34 126 211 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 126 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 126 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 126 211 (accept_3_3 32 126 211
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 126 211 (Polychromatic418967fa.accept_13_5_9_3_1_870
  31 126 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 126 211
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 30 126 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 126 211 (accept_3_3 29 126 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 126 211 (Polychromatic418967fa.accept_13_2_9_3_1_2212 28 126 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 126 211 (Polychromatic418967fa.accept_10_7_6_1_1_486 27 126 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 126 211 (accept_3_3 26 126 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 126 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 126 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 126 211
  (Polychromatic418967fa.accept_15_9_6_1_1_493 24 126 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 126 211 (accept_3_3 23 126 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 126 211 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 126 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 126 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 126 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 126 211 (accept_3_3 20 126 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 126 211 (Polychromatic418967fa.accept_11_8_5_2_1_1629 19 126 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 126 211
  (Polychromatic418967fa.accept_13_5_9_3_1_870 18 126 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 126 211 (accept_3_3 17 126 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 126 211 (Polychromatic418967fa.accept_20_16_6_11_1_9657 16 126 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 126 211 (Polychromatic418967fa.accept_10_5_6_1_1_836 15 126 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 126 211 (accept_3_3 14 126 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 126 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 126 211
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 126 211
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 126 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 126 211 (accept_3_3 11 126 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 126 211 (Polychromatic418967fa.accept_15_10_6_1_1_3707 10 126 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 126 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 126 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 126 211 (accept_3_3 8 126 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 126 211 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 126 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 126 211
  (Polychromatic418967fa.accept_13_6_9_3_1_915 6 126 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 126 211 (accept_3_3 5 126 211 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  126 211 (Polychromatic418967fa.accept_19_4_12_2_1_11158 4 126 211 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 126 211 (Polychromatic418967fa.accept_15_3_6_1_1_1834 3 126 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 126 211 (accept_3_3 2 126 211 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 126 211 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 126 211 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  211))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_211_segment_000)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


