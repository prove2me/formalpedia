-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch149
-- name    : Polychromatic418967fa_Branch149
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:15:45.90234+00:00
-- url     : https://prove2.me/theorems/f3cee2cf-1eb8-4483-af8b-954b7a559edc
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

def Polychromatic418967fa.branch_149 : allB 149 149 :=
  allB_succ' 2 148 149 (Eq.refl Bool.true) (allA_of_3_0 2 148 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  147 149 (Eq.refl Bool.true) (allA_succ_of_accept 2 147 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 147 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 149 (accept_3_2 1 147 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 147 149))) (allB_succ' 4 146 149 (Eq.refl Bool.true)
  (allA_succ_of_accept 3 146 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 146 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 146 149 (Polychromatic418967fa.accept_19_2_13_16_1_5089 2 146
  149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 146 149 (accept_3_2 1 146 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146 149)))) (allB_succ' 5 145 149 (Eq.refl Bool.true) (allA_of_3_0
  5 145 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 6 144 149 (Eq.refl Bool.true) (allA_succ_of_accept 5
  144 149 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 144 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 144 149 (accept_3_2 4 144 149 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 144 149 (Polychromatic418967fa.accept_10_3_4_9_1_15 3 144 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 144 149 (Polychromatic418967fa.accept_13_2_1_6_1_2365 2 144 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 144 149 (accept_3_2 1 144 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144 149)))))) (allB_succ' 7 143 149 (Eq.refl Bool.true)
  (allA_succ_of_accept 6 143 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 143 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 143 149 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 143 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 143 149 (accept_3_2 4 143 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 143 149 (Polychromatic418967fa.accept_9_3_8_5_1_65 3
  143 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 143 149
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 143 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 143 149 (accept_3_2 1 143 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 143 149)))))))
  (allB_succ' 8 142 149 (Eq.refl Bool.true) (allA_of_3_0 8 142 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  9 141 149 (Eq.refl Bool.true) (allA_succ_of_accept 8 141 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 141 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 149 (accept_3_2 7 141 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 141 149 (Polychromatic418967fa.accept_7_6_1_2_1_230 6
  141 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 141 149
  (Polychromatic418967fa.accept_10_5_1_9_1_791 5 141 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 141 149 (accept_3_2 4 141 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  141 149 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 141 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 141 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 141 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 149 (accept_3_2 1 141 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 141 149))))))))) (allB_succ' 10 140 149 (Eq.refl Bool.true) (allA_succ_of_accept 9 140
  149 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 140 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 140 149 (Polychromatic418967fa.accept_15_8_5_14_1_986 8 140 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 140 149 (accept_3_2 7 140 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 140 149 (Polychromatic418967fa.accept_15_6_5_14_1_429 6 140 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 140 149 (Polychromatic418967fa.accept_13_5_10_6_1_2361
  5 140 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 140 149 (accept_3_2 4
  140 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 140 149
  (Polychromatic418967fa.accept_6_3_2_5_1_32 3 140 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 140 149 (Polychromatic418967fa.accept_12_2_8_5_1_408 2 140 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 140 149 (accept_3_2 1 140 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 140 149)))))))))) (allB_succ' 11 139 149 (Eq.refl Bool.true) (allA_of_3_0 11 139 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 12 138 149 (Eq.refl Bool.true) (allA_succ_of_accept 11 138 149
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 138 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 138 149 (accept_3_2 10 138 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  138 149 (Polychromatic418967fa.accept_18_9_12_5_1_864 9 138 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 138 149 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 138 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 138 149 (accept_3_2 7 138 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 138 149 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 138 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 138 149
  (Polychromatic418967fa.accept_27_5_3_14_1_8014 5 138 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 138 149 (accept_3_2 4 138 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  138 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 138 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 138 149 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 138 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 138 149 (accept_3_2 1 138 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 138 149)))))))))))) (allB_succ' 13 137 149 (Eq.refl Bool.true) (allA_succ_of_accept 12
  137 149 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 137 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 137 149 (Polychromatic418967fa.accept_16_11_9_5_1_4412 11 137 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 137 149 (accept_3_2 10 137 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 137 149 (Polychromatic418967fa.accept_13_9_7_6_1_1673 9 137 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 149
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 137 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 137 149 (accept_3_2 7 137 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  137 149 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 137 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 137 149 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 137 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 149 (accept_3_2 4 137 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 137 149 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 137 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 137 149
  (Polychromatic418967fa.accept_10_2_7_9_1_783 2 137 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 137 149 (accept_3_2 1 137 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 137
  149))))))))))))) (allB_succ' 14 136 149 (Eq.refl Bool.true) (allA_of_3_0 14 136 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 135 149 (Eq.refl Bool.true) (allA_succ_of_accept 14 135 149
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 135 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 135 149 (accept_3_2 13 135 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 135 149 (Polychromatic418967fa.accept_13_12_5_6_1_1050 12 135 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 135 149 (Polychromatic418967fa.accept_10_1_5_9_1_157 11 135 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 135 149 (accept_3_2 10 135 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 135 149 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 135 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 135 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 135 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 135 149 (accept_3_2 7 135 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  135 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 135 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 135 149 (Polychromatic418967fa.accept_19_5_2_16_1_8013 5 135 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 135 149 (accept_3_2 4 135 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 135 149 (Polychromatic418967fa.accept_13_3_5_6_1_3192 3 135 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 135 149
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 135 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 135 149 (accept_3_2 1 135 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135
  149))))))))))))))) (allB_succ' 16 134 149 (Eq.refl Bool.true) (allA_succ_of_accept 15 134 149
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 134 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 134 149 (Polychromatic418967fa.accept_18_14_8_5_1_860 14 134 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 134 149 (accept_3_2 13 134 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 134 149 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 134 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 134 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 11
  134 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 134 149 (accept_3_2 10
  134 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 134 149
  (Polychromatic418967fa.accept_6_3_2_5_1_32 9 134 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 134 149 (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 134 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 134 149 (accept_3_2 7 134 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 134 149 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 134 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 134 149 (Polychromatic418967fa.accept_10_5_4_9_1_420 5
  134 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 134 149 (accept_3_2 4 134
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 134 149 (Polychromatic418967fa.accept_4_3_2_1_1_50
  3 134 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 134 149
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 134 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 134 149 (accept_3_2 1 134 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134
  149)))))))))))))))) (allB_succ' 17 133 149 (Eq.refl Bool.true) (allA_of_3_0 17 133 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 18 132 149 (Eq.refl Bool.true) (allA_succ_of_accept 17 132 149
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 132 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 132 149 (accept_3_2 16 132 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 132 149 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 132 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 132 149 (Polychromatic418967fa.accept_13_1_2_6_1_515 14 132 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 132 149 (accept_3_2 13 132 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 132 149 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 132 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 132 149
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 132 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 132 149 (accept_3_2 10 132 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  132 149 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 132 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 132 149 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 132 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 132 149 (accept_3_2 7 132 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 132 149 (Polychromatic418967fa.accept_16_6_4_5_1_2272 6 132 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 132 149
  (Polychromatic418967fa.accept_23_5_17_11_1_8012 5 132 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 132 149 (accept_3_2 4 132 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  132 149 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 132 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 132 149 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 132 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 132 149 (accept_3_2 1 132 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 132 149)))))))))))))))))) (allB_succ' 19 131 149 (Eq.refl Bool.true)
  (allA_succ_of_accept 18 131 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 131 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 131 149 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 131 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 131 149 (accept_3_2 16 131 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 131 149 (Polychromatic418967fa.accept_10_5_1_9_1_791
  15 131 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 131 149
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 131 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 131 149 (accept_3_2 13 131 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 131 149 (Polychromatic418967fa.accept_10_2_1_9_1_1248 12 131 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 131 149 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 131 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 131 149 (accept_3_2 10 131 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 131 149 (Polychromatic418967fa.accept_13_9_1_6_1_510 9 131 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 131 149
  (Polychromatic418967fa.accept_10_8_1_9_1_413 8 131 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 131 149 (accept_3_2 7 131 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  131 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 131 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 131 149 (Polychromatic418967fa.accept_10_5_1_9_1_791 5 131 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 131 149 (accept_3_2 4 131 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 131 149 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 131 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 131 149
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 131 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 131 149 (accept_3_2 1 131 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 131
  149))))))))))))))))))) (allB_succ' 20 130 149 (Eq.refl Bool.true) (allA_of_3_0 20 130 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 21 129 149 (Eq.refl Bool.true) (allA_succ_of_accept 20 129 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 129 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 129 149 (accept_3_2 19 129 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 129 149 (Polychromatic418967fa.accept_13_5_12_6_1_508 18 129 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 129 149 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 129 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 149 (accept_3_2 16 129 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 129 149 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 129 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 129 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 129 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 129 149 (accept_3_2 13 129 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 129 149 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 129 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 129 149 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 129 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 149 (accept_3_2 10 129 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 129 149 (Polychromatic418967fa.accept_16_9_1_5_1_2282 9 129 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 129 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 129 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 129 149 (accept_3_2 7 129 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  129 149 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 129 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 129 149 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 129 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 149 (accept_3_2 4 129 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 129 149 (Polychromatic418967fa.accept_11_3_8_6_1_788 3 129 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 129 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 129 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 129 149 (accept_3_2 1 129 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129
  149))))))))))))))))))))) (allB_succ' 22 128 149 (Eq.refl Bool.true) (allA_succ_of_accept 21 128 149
  (Polychromatic418967fa.accept_6_3_2_5_1_32 21 128 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 128 149 (Polychromatic418967fa.accept_15_5_8_14_1_432 20 128 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 128 149 (accept_3_2 19 128 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 128 149 (Polychromatic418967fa.accept_13_5_11_6_1_505 18 128 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 128 149
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 128 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 128 149 (accept_3_2 16 128 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 128 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 128 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 128 149 (Polychromatic418967fa.accept_10_4_8_9_1_784 14 128 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 128 149 (accept_3_2 13 128 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 128 149 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 128 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 128 149
  (Polychromatic418967fa.accept_10_1_8_9_1_787 11 128 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 128 149 (accept_3_2 10 128 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  128 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 128 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 128 149 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 128 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 128 149 (accept_3_2 7 128 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 128 149 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 128 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 128 149
  (Polychromatic418967fa.accept_13_5_11_6_1_505 5 128 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 128 149 (accept_3_2 4 128 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  128 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 128 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 128 149 (Polychromatic418967fa.accept_12_2_8_5_1_408 2 128 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 128 149 (accept_3_2 1 128 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 128 149)))))))))))))))))))))) (allB_succ' 23 127 149 (Eq.refl Bool.true) (allA_of_3_0
  23 127 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 126 149 (Eq.refl Bool.true) (allA_succ_of_accept 23
  126 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 126 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 126 149 (accept_3_2 22 126 149 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 126 149 (Polychromatic418967fa.accept_11_10_5_6_1_1842 21 126 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 126 149 (Polychromatic418967fa.accept_13_7_9_6_1_148 20 126
  149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 126 149 (accept_3_2 19 126
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 126 149
  (Polychromatic418967fa.accept_22_18_16_17_1_8011 18 126 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 126 149 (Polychromatic418967fa.accept_13_4_9_6_1_2376 17 126 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 126 149 (accept_3_2 16 126 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 126 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 126 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 126 149
  (Polychromatic418967fa.accept_13_1_9_6_1_146 14 126 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 126 149 (accept_3_2 13 126 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 126 149 (Polychromatic418967fa.accept_11_1_5_6_1_397 12 126 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 126 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 126 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 126 149 (accept_3_2 10 126 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 126 149 (Polychromatic418967fa.accept_15_9_6_14_1_2627 9 126 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 126 149
  (Polychromatic418967fa.accept_15_8_6_14_1_975 8 126 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 126 149 (accept_3_2 7 126 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  126 149 (Polychromatic418967fa.accept_17_6_7_13_1_3062 6 126 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 126 149 (Polychromatic418967fa.accept_10_5_6_9_1_2235 5 126 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 126 149 (accept_3_2 4 126 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 126 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 126 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 126 149
  (Polychromatic418967fa.accept_13_2_9_6_1_501 2 126 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 126 149 (accept_3_2 1 126 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  149)))))))))))))))))))))))) (allB_succ' 25 125 149 (Eq.refl Bool.true) (allA_succ_of_accept 24 125 149
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 125 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 125 149 (Polychromatic418967fa.accept_15_8_5_14_1_986 23 125 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 125 149 (accept_3_2 22 125 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 125 149 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 125 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 125 149 (Polychromatic418967fa.accept_9_2_8_5_1_228
  20 125 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 125 149 (accept_3_2 19
  125 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 125 149
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 125 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 125 149 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 125 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 125 149 (accept_3_2 16 125 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 125 149 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 125 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 125 149 (Polychromatic418967fa.accept_10_4_5_9_1_1231
  14 125 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 125 149 (accept_3_2 13
  125 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 125 149
  (Polychromatic418967fa.accept_9_3_8_5_1_65 12 125 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 125 149 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 125 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 125 149 (accept_3_2 10 125 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 125 149 (Polychromatic418967fa.accept_15_9_5_14_1_973 9 125 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 125 149 (Polychromatic418967fa.accept_7_1_6_2_1_18 8
  125 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 125 149 (accept_3_2 7 125
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 125 149
  (Polychromatic418967fa.accept_9_6_8_5_1_837 6 125 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 125 149 (Polychromatic418967fa.accept_19_5_11_16_1_8010 5 125 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 125 149 (accept_3_2 4 125 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 125 149 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 125 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 125 149 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  125 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 125 149 (accept_3_2 1 125
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 125 149))))))))))))))))))))))))) (allB_succ' 26 124 149
  (Eq.refl Bool.true) (allA_of_3_0 26 124 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 27 123 149 (Eq.refl
  Bool.true) (allA_succ_of_accept 26 123 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 123 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 149 (accept_3_2 25 123 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 123 149 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 123 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 123 149
  (Polychromatic418967fa.accept_16_7_11_5_1_4402 23 123 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 123 149 (accept_3_2 22 123 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 123 149 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 123 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 123 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 123 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 149 (accept_3_2 19 123 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 123 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 123 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 123 149
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 123 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 123 149 (accept_3_2 16 123 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 123 149 (Polychromatic418967fa.accept_11_4_2_6_1_389 15 123 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 123 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 123 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 149 (accept_3_2 13 123 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 123 149 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 123 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 123 149
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 123 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 123 149 (accept_3_2 10 123 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  123 149 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 123 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 123 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 123 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 149 (accept_3_2 7 123 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 123 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 123 149
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 123 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 123 149 (accept_3_2 4 123 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  123 149 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 123 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 123 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 123 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 149 (accept_3_2 1 123 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 123 149))))))))))))))))))))))))))) (allB_succ' 28 122 149 (Eq.refl Bool.true)
  (allA_succ_of_accept 27 122 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 122 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 122 149 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 122 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 122 149 (accept_3_2 25 122 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 122 149 (Polychromatic418967fa.accept_13_11_5_6_1_519
  24 122 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 122 149
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 122 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 122 149 (accept_3_2 22 122 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 122 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 122 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 122 149 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 122 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 122 149 (accept_3_2 19 122 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 122 149 (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 122 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 122 149
  (Polychromatic418967fa.accept_10_7_2_9_1_775 17 122 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 122 149 (accept_3_2 16 122 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 122 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 122 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 122 149 (Polychromatic418967fa.accept_13_1_5_6_1_1048 14 122 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 122 149 (accept_3_2 13 122 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 122 149 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 122 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 122 149
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 122 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 122 149 (accept_3_2 10 122 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  122 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 122 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 122 149 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 122 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 122 149 (accept_3_2 7 122 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 122 149 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 122 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 122 149
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 122 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 122 149 (accept_3_2 4 122 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  122 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 122 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 122 149 (Polychromatic418967fa.accept_25_2_22_24_1_8009 2 122 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 122 149 (accept_3_2 1 122 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 122 149)))))))))))))))))))))))))))) (allB_succ' 29 121 149 (Eq.refl
  Bool.true) (allA_of_3_0 29 121 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 30 120 149 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 120 149 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 120 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 120 149 (accept_3_2 28 120 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 120 149 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 120 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 120 149 (Polychromatic418967fa.accept_9_8_3_5_1_241
  26 120 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 120 149 (accept_3_2 25
  120 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 120 149
  (Polychromatic418967fa.accept_7_3_1_2_1_247 24 120 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 120 149 (Polychromatic418967fa.accept_13_10_3_6_1_1003 23 120 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 120 149 (accept_3_2 22 120 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 120 149 (Polychromatic418967fa.accept_22_21_10_17_1_8008 21 120 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 120 149
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 120 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 120 149 (accept_3_2 19 120 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 120 149 (Polychromatic418967fa.accept_13_5_3_6_1_3278 18 120 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 120 149 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 120 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 120 149 (accept_3_2 16 120 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 120 149 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 120 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 120 149
  (Polychromatic418967fa.accept_13_1_3_6_1_158 14 120 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 120 149 (accept_3_2 13 120 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 120 149 (Polychromatic418967fa.accept_16_12_8_5_1_3316 12 120 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 120 149 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 120 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 120 149 (accept_3_2 10 120 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 120 149 (Polychromatic418967fa.accept_13_9_3_6_1_1661 9 120 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 120 149
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 120 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 120 149 (accept_3_2 7 120 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  120 149 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 120 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 120 149 (Polychromatic418967fa.accept_11_5_10_6_1_793 5 120 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 120 149 (accept_3_2 4 120 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 120 149 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 120 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 120 149
  (Polychromatic418967fa.accept_9_2_3_5_1_60 2 120 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 120 149 (accept_3_2 1 120 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  149)))))))))))))))))))))))))))))) (allB_succ' 31 119 149 (Eq.refl Bool.true) (allA_succ_of_accept 30 119 149
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 119 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 119 149 (Polychromatic418967fa.accept_19_10_5_16_1_6522 29 119 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 119 149 (accept_3_2 28 119 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 119 149 (Polychromatic418967fa.accept_13_1_2_6_1_515 27 119 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 119 149
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 119 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 119 149 (accept_3_2 25 119 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 119 149 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 119 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 119 149 (Polychromatic418967fa.accept_13_10_2_6_1_1044 23 119 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 119 149 (accept_3_2 22 119 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 119 149 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 119 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 119 149
  (Polychromatic418967fa.accept_19_1_5_16_1_2587 20 119 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 119 149 (accept_3_2 19 119 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 119 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 119 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 119 149 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 119 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 119 149 (accept_3_2 16 119 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 119 149 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 119 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 119 149
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 119 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 119 149 (accept_3_2 13 119 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 119 149 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 119 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 119 149 (Polychromatic418967fa.accept_16_11_7_5_1_4364 11 119 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 149 (accept_3_2 10 119 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 119 149 (Polychromatic418967fa.accept_13_9_2_6_1_514 9 119 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 149
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 119 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 119 149 (accept_3_2 7 119 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  119 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 119 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 119 149 (Polychromatic418967fa.accept_14_5_7_9_1_3828 5 119 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 149 (accept_3_2 4 119 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 119 149 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 119 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 149
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 119 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 119 149 (accept_3_2 1 119 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  149))))))))))))))))))))))))))))))) (allB_succ' 32 118 149 (Eq.refl Bool.true) (allA_of_3_0 32 118 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 117 149 (Eq.refl Bool.true) (allA_succ_of_accept 32 117 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 117 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 117 149 (accept_3_2 31 117 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 117 149 (Polychromatic418967fa.accept_18_12_9_5_1_2771 30 117 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 117 149 (Polychromatic418967fa.accept_25_4_17_24_1_8007 29 117 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 149 (accept_3_2 28 117 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 117 149 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 117
  149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 117 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 117 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 117 149 (accept_3_2 25 117 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 117 149 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 117 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 117 149 (Polychromatic418967fa.accept_11_1_7_6_1_378 23 117 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 149 (accept_3_2 22 117 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 117 149 (Polychromatic418967fa.accept_14_7_5_9_1_2911 21 117
  149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 117 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 117 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 117 149 (accept_3_2 19 117 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 117 149 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 117 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 117 149 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 117 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 149 (accept_3_2 16 117 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 117 149 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 117 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 117 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 117 149 (accept_3_2 13 117 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 117 149 (Polychromatic418967fa.accept_10_2_7_9_1_783 12 117 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 117 149 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 117 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 149 (accept_3_2 10 117 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 149 (Polychromatic418967fa.accept_15_9_12_14_1_963 9 117 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 117 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 117 149 (accept_3_2 7 117 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  117 149 (Polychromatic418967fa.accept_19_6_3_16_1_8006 6 117 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 117 149 (Polychromatic418967fa.accept_17_5_15_13_1_7936 5 117 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 149 (accept_3_2 4 117 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 117 149 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 117 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 117 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 117 149 (accept_3_2 1 117 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  149))))))))))))))))))))))))))))))))) (allB_succ' 34 116 149 (Eq.refl Bool.true) (allA_succ_of_accept 33 116 149
  (Polychromatic418967fa.accept_6_3_2_5_1_32 33 116 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 116 149 (Polychromatic418967fa.accept_18_14_8_5_1_860 32 116 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 116 149 (accept_3_2 31 116 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 116 149 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 116 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 116 149 (Polychromatic418967fa.accept_9_2_8_5_1_228
  29 116 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 116 149 (accept_3_2 28
  116 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 116 149
  (Polychromatic418967fa.accept_6_3_2_5_1_32 27 116 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 116 149 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 116 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 116 149 (accept_3_2 25 116 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 116 149 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 116 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 116 149 (Polychromatic418967fa.accept_10_3_6_9_1_779
  23 116 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 116 149 (accept_3_2 22
  116 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 116 149
  (Polychromatic418967fa.accept_6_3_2_5_1_32 21 116 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 116 149 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 116 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 116 149 (accept_3_2 19 116 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 116 149 (Polychromatic418967fa.accept_13_5_12_6_1_508 18 116 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 116 149
  (Polychromatic418967fa.accept_8_1_4_5_1_48 17 116 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 116 149 (accept_3_2 16 116 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 116 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 116 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 116 149 (Polychromatic418967fa.accept_12_2_8_5_1_408 14 116 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 116 149 (accept_3_2 13 116 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 116 149 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 116 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 116 149
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 116 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 116 149 (accept_3_2 10 116 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  116 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 116 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 116 149 (Polychromatic418967fa.accept_16_8_4_5_1_4379 8 116 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 116 149 (accept_3_2 7 116 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 116 149 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 116 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 116 149
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 116 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 116 149 (accept_3_2 4 116 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  116 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 116 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 116 149 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 116 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 116 149 (accept_3_2 1 116 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 116 149)))))))))))))))))))))))))))))))))) (allB_succ' 35 115 149 (Eq.refl Bool.true)
  (allA_of_3_0 35 115 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 114 149 (Eq.refl Bool.true)
  (allA_succ_of_accept 35 114 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 114 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 114 149 (accept_3_2 34 114 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 114 149 (Polychromatic418967fa.accept_10_3_4_9_1_15 33 114 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 114 149 (Polychromatic418967fa.accept_14_4_2_9_1_2092
  32 114 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 114 149 (accept_3_2 31
  114 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 114 149
  (Polychromatic418967fa.accept_9_3_6_5_1_63 30 114 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 114 149 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 114 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 114 149 (accept_3_2 28 114 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 114 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 114 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 114 149 (Polychromatic418967fa.accept_9_8_6_5_1_513
  26 114 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 114 149 (accept_3_2 25
  114 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 114 149
  (Polychromatic418967fa.accept_11_2_4_6_1_2412 24 114 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 114 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 114 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 114 149 (accept_3_2 22 114 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 114 149 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 114 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 114 149 (Polychromatic418967fa.accept_9_2_6_5_1_227
  20 114 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 114 149 (accept_3_2 19
  114 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 114 149
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 114 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 114 149 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 114 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 114 149 (accept_3_2 16 114 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 114 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 114 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 114 149
  (Polychromatic418967fa.accept_21_14_9_2_1_8005 14 114 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 114 149 (accept_3_2 13 114 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 114 149 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 114 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 114 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 114 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 114 149 (accept_3_2 10 114 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 114 149 (Polychromatic418967fa.accept_13_9_10_6_1_1028 9 114 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 114 149
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 114 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 114 149 (accept_3_2 7 114 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  114 149 (Polychromatic418967fa.accept_15_6_9_14_1_3457 6 114 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 114 149 (Polychromatic418967fa.accept_10_5_4_9_1_420 5 114 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 114 149 (accept_3_2 4 114 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 114 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 114 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 114 149
  (Polychromatic418967fa.accept_9_2_6_5_1_227 2 114 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 114 149 (accept_3_2 1 114 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  149)))))))))))))))))))))))))))))))))))) (allB_succ' 37 113 149 (Eq.refl Bool.true) (allA_succ_of_accept 36 113 149
  (Polychromatic418967fa.accept_8_4_1_5_1_186 36 113 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 113 149 (Polychromatic418967fa.accept_15_5_8_14_1_432 35 113 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 113 149 (accept_3_2 34 113 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 113 149 (Polychromatic418967fa.accept_13_7_9_6_1_148 33 113 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 113 149
  (Polychromatic418967fa.accept_17_15_11_13_1_2039 32 113 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 113 149 (accept_3_2 31 113 149 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 113 149 (Polychromatic418967fa.accept_11_8_3_6_1_1855 30 113 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 113 149 (Polychromatic418967fa.accept_13_3_9_6_1_502 29 113
  149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 113 149 (accept_3_2 28 113
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 113 149
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 113 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 113 149 (Polychromatic418967fa.accept_10_6_3_9_1_1207 26 113 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 113 149 (accept_3_2 25 113 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 113 149 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 113 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 113 149
  (Polychromatic418967fa.accept_13_10_9_6_1_1026 23 113 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 113 149 (accept_3_2 22 113 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 113 149 (Polychromatic418967fa.accept_15_6_8_14_1_4575 21 113 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 113 149 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 113 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 113 149 (accept_3_2 19 113 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 113 149 (Polychromatic418967fa.accept_27_18_5_14_1_3959 18 113 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 113 149
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 113 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 113 149 (accept_3_2 16 113 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 113 149 (Polychromatic418967fa.accept_13_2_9_6_1_501 15 113 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 113 149 (Polychromatic418967fa.accept_10_4_3_9_1_1262 14 113 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 113 149 (accept_3_2 13 113 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 113 149 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 113 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 113 149
  (Polychromatic418967fa.accept_24_11_17_5_1_7968 11 113 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 113 149 (accept_3_2 10 113 149 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 113 149 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 113 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 149 (Polychromatic418967fa.accept_11_8_3_6_1_1855 8 113 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 113 149 (accept_3_2 7 113 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 113 149 (Polychromatic418967fa.accept_7_6_1_2_1_230 6
  113 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 113 149
  (Polychromatic418967fa.accept_15_5_8_14_1_432 5 113 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 113 149 (accept_3_2 4 113 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  113 149 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 113 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 113 149 (Polychromatic418967fa.accept_13_2_9_6_1_501 2 113 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 113 149 (accept_3_2 1 113 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 113 149))))))))))))))))))))))))))))))))))))) (allB_succ' 38 112 149 (Eq.refl Bool.true)
  (allA_of_3_0 38 112 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 111 149 (Eq.refl Bool.true)
  (allA_succ_of_accept 38 111 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 111 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 149 (accept_3_2 37 111 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 111 149 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 111 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 111 149 (Polychromatic418967fa.accept_9_8_3_5_1_241
  35 111 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 111 149 (accept_3_2 34
  111 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 111 149
  (Polychromatic418967fa.accept_9_6_3_5_1_240 33 111 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 111 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 111 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 149 (accept_3_2 31 111 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 111 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 111 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 111 149 (Polychromatic418967fa.accept_7_1_6_2_1_18 29
  111 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 149 (accept_3_2 28
  111 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 111 149
  (Polychromatic418967fa.accept_11_5_1_6_1_774 27 111 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 111 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 111 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 149 (accept_3_2 25 111 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 111 149 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 111 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 111 149 (Polychromatic418967fa.accept_15_8_6_14_1_975
  23 111 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 111 149 (accept_3_2 22
  111 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 111 149
  (Polychromatic418967fa.accept_12_9_3_5_1_423 21 111 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 111 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 111 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 149 (accept_3_2 19 111 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 111 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 111 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 149 (Polychromatic418967fa.accept_7_3_6_2_1_90 17
  111 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 149 (accept_3_2 16
  111 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 111 149
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 111 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 111 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 111 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 149 (accept_3_2 13 111 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 111 149 (Polychromatic418967fa.accept_10_2_1_9_1_1248 12 111 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 149
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 111 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 111 149 (accept_3_2 10 111 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  111 149 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 111 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 111 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 111 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 149 (accept_3_2 7 111 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 111 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 149
  (Polychromatic418967fa.accept_10_5_1_9_1_791 5 111 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 111 149 (accept_3_2 4 111 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  111 149 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 111 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 111 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 111 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 149 (accept_3_2 1 111 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 111 149))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 110 149 (Eq.refl
  Bool.true) (allA_succ_of_accept 39 110 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 110 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 110 149 (Polychromatic418967fa.accept_7_3_5_2_1_17 38
  110 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 110 149 (accept_3_2 37
  110 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 110 149
  (Polychromatic418967fa.accept_15_6_5_14_1_429 36 110 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 110 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 110 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 110 149 (accept_3_2 34 110 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 110 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 110 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 110 149 (Polychromatic418967fa.accept_7_4_5_2_1_243
  32 110 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 110 149 (accept_3_2 31
  110 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 110 149
  (Polychromatic418967fa.accept_9_3_2_5_1_234 30 110 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 110 149 (Polychromatic418967fa.accept_21_8_5_2_1_8004 29 110 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 110 149 (accept_3_2 28 110 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 110 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 110 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 110 149 (Polychromatic418967fa.accept_9_8_2_5_1_237
  26 110 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 110 149 (accept_3_2 25
  110 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 110 149
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 110 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 110 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 110 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 110 149 (accept_3_2 22 110 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 110 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 110 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 110 149 (Polychromatic418967fa.accept_12_8_2_5_1_844
  20 110 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 110 149 (accept_3_2 19
  110 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 110 149
  (Polychromatic418967fa.accept_7_4_5_2_1_243 18 110 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 110 149 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 110 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 110 149 (accept_3_2 16 110 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 110 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 110 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 110 149
  (Polychromatic418967fa.accept_25_14_10_24_1_8003 14 110 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 110 149 (accept_3_2 13 110 149 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 110 149 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 110 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 110 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 110 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 110 149 (accept_3_2 10 110 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 110 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 9
  110 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 110 149
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 110 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 110 149 (accept_3_2 7 110 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  110 149 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 110 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 110 149 (Polychromatic418967fa.accept_17_5_8_13_1_7994 5 110 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 110 149 (accept_3_2 4 110 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 110 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 110 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 110 149
  (Polychromatic418967fa.accept_15_2_5_14_1_61 2 110 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 110 149 (accept_3_2 1 110 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  149)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 109 149 (Eq.refl Bool.true) (allA_of_3_0 41 109 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 108 149 (Eq.refl Bool.true) (allA_succ_of_accept 41 108 149
  (Polychromatic418967fa.accept_7_6_3_2_1_461 41 108 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 108 149 (accept_3_2 40 108 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 108 149 (Polychromatic418967fa.accept_16_7_12_5_1_734 39 108 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 108 149 (Polychromatic418967fa.accept_21_17_3_2_1_2111 38 108 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 108 149 (accept_3_2 37 108 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 108 149 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 108 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 108 149
  (Polychromatic418967fa.accept_13_9_4_6_1_1005 35 108 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 108 149 (accept_3_2 34 108 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 108 149 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 108 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 108 149 (Polychromatic418967fa.accept_15_2_3_14_1_972 32 108 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 108 149 (accept_3_2 31 108 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 108 149 (Polychromatic418967fa.accept_19_11_13_16_1_8002 30
  108 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 108 149
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 108 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 108 149 (accept_3_2 28 108 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 108 149 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 108 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 108 149 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 108 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 108 149 (accept_3_2 25 108 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 108 149 (Polychromatic418967fa.accept_10_4_8_9_1_784 24 108 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 108 149
  (Polychromatic418967fa.accept_13_10_4_6_1_3224 23 108 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 108 149 (accept_3_2 22 108 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 108 149 (Polychromatic418967fa.accept_10_1_8_9_1_787 21 108 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 108 149 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 108 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 108 149 (accept_3_2 19 108 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 108 149 (Polychromatic418967fa.accept_13_5_4_6_1_2371 18 108 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 108 149
  (Polychromatic418967fa.accept_8_1_4_5_1_48 17 108 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 108 149 (accept_3_2 16 108 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 108 149 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 108 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 108 149 (Polychromatic418967fa.accept_10_4_8_9_1_784 14 108 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 108 149 (accept_3_2 13 108 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 108 149 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 108 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 108 149
  (Polychromatic418967fa.accept_10_1_8_9_1_787 11 108 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 108 149 (accept_3_2 10 108 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  108 149 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 108 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 108 149 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 108 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 108 149 (accept_3_2 7 108 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 108 149 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 108 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 108 149
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 108 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 108 149 (accept_3_2 4 108 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  108 149 (Polychromatic418967fa.accept_11_3_9_6_1_105 3 108 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 108 149 (Polychromatic418967fa.accept_13_2_4_6_1_2356 2 108 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 108 149 (accept_3_2 1 108 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 108 149)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 107 149 (Eq.refl
  Bool.true) (allA_succ_of_accept 42 107 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 107 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 107 149
  (Polychromatic418967fa.accept_16_9_11_5_1_2279 41 107 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 107 149 (accept_3_2 40 107 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 107 149 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 107 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 107 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 107 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 107 149 (accept_3_2 37 107 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 107 149 (Polychromatic418967fa.accept_11_3_8_6_1_788 36 107 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 107 149
  (Polychromatic418967fa.accept_13_9_3_6_1_1661 35 107 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 107 149 (accept_3_2 34 107 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 107 149 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 107 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 107 149 (Polychromatic418967fa.accept_10_2_7_9_1_783 32 107 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 107 149 (accept_3_2 31 107 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 107 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 107 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 107 149
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 107 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 107 149 (accept_3_2 28 107 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 107 149 (Polychromatic418967fa.accept_13_1_3_6_1_158 27 107 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 107 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 107 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 107 149 (accept_3_2 25 107 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 107 149 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 107 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 107 149
  (Polychromatic418967fa.accept_13_10_3_6_1_1003 23 107 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 107 149 (accept_3_2 22 107 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 107 149 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 107 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 107 149 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 107 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 107 149 (accept_3_2 19 107 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 107 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 107 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 107 149
  (Polychromatic418967fa.accept_20_17_7_9_1_8001 17 107 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 107 149 (accept_3_2 16 107 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 107 149 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 107 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 107 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 107 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 107 149 (accept_3_2 13 107 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 107 149 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 107 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 107 149
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 107 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 107 149 (accept_3_2 10 107 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  107 149 (Polychromatic418967fa.accept_13_9_3_6_1_1661 9 107 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 107 149 (Polychromatic418967fa.accept_10_8_7_9_1_425 8 107 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 107 149 (accept_3_2 7 107 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 107 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 107 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 107 149
  (Polychromatic418967fa.accept_13_5_3_6_1_3278 5 107 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 107 149 (accept_3_2 4 107 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  107 149 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 107 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 107 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 107 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 107 149 (accept_3_2 1 107 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 107 149))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 106 149 (Eq.refl
  Bool.true) (allA_of_3_0 44 106 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 105 149 (Eq.refl Bool.true)
  (allA_succ_of_accept 44 105 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 105 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 149 (accept_3_2 43 105 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 105 149 (Polychromatic418967fa.accept_13_3_1_6_1_509 42 105 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 105 149
  (Polychromatic418967fa.accept_10_1_5_9_1_157 41 105 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 105 149 (accept_3_2 40 105 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 105 149 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 105 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 105 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 105 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 149 (accept_3_2 37 105 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 105 149 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 105 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 105 149
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 105 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 105 149 (accept_3_2 34 105 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 105 149 (Polychromatic418967fa.accept_13_7_1_6_1_3287 33 105 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 105 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 105 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 149 (accept_3_2 31 105 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 105 149 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 105 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 105 149
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 105 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 105 149 (accept_3_2 28 105 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 105 149 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 105 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 105 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 105 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 149 (accept_3_2 25 105 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 105 149 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 105 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 105 149
  (Polychromatic418967fa.accept_19_4_10_16_1_6531 23 105 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 105 149 (accept_3_2 22 105 149 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 105 149 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 105 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 105 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 105 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 149 (accept_3_2 19 105 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 149 (Polychromatic418967fa.accept_13_5_1_6_1_2367
  18 105 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 149
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 105 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 105 149 (accept_3_2 16 105 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 105 149 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 105 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 105 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 105 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 149 (accept_3_2 13 105 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 149 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 105 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 149
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 105 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 105 149 (accept_3_2 10 105 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  105 149 (Polychromatic418967fa.accept_13_9_1_6_1_510 9 105 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 105 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 105 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 149 (accept_3_2 7 105 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 105 149 (Polychromatic418967fa.accept_10_6_5_9_1_1233 6 105 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 105 149
  (Polychromatic418967fa.accept_13_5_1_6_1_2367 5 105 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 105 149 (accept_3_2 4 105 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  105 149 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 105 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 105 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 105 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 149 (accept_3_2 1 105 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 105 149))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 104 149 (Eq.refl
  Bool.true) (allA_succ_of_accept 45 104 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 104 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 104 149
  (Polychromatic418967fa.accept_16_12_8_5_1_3316 44 104 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 104 149 (accept_3_2 43 104 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 104 149 (Polychromatic418967fa.accept_19_4_9_16_1_3811 42 104 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 104 149 (Polychromatic418967fa.accept_17_7_2_13_1_5397 41 104 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 104 149 (accept_3_2 40 104 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 104 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 104 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 104 149
  (Polychromatic418967fa.accept_7_3_6_2_1_90 38 104 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 104 149 (accept_3_2 37 104 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 104 149 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 104 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 104 149 (Polychromatic418967fa.accept_10_5_4_9_1_420 35 104 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 104 149 (accept_3_2 34 104 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 104 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 104 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 104 149
  (Polychromatic418967fa.accept_7_4_6_2_1_451 32 104 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 104 149 (accept_3_2 31 104 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 104 149 (Polychromatic418967fa.accept_21_9_20_2_1_8000 30 104 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 104 149 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 104 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 104 149 (accept_3_2 28 104 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 104 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 104 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 104 149
  (Polychromatic418967fa.accept_12_2_8_5_1_408 26 104 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 104 149 (accept_3_2 25 104 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 104 149 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 104 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 104 149 (Polychromatic418967fa.accept_10_3_4_9_1_15 23 104 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 104 149 (accept_3_2 22 104 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 104 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 104 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 104 149
  (Polychromatic418967fa.accept_16_4_8_5_1_3317 20 104 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 104 149 (accept_3_2 19 104 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 104 149 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 104 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 104 149 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 104 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 104 149 (accept_3_2 16 104 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 104 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 104 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 104 149
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 104 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 104 149 (accept_3_2 13 104 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 104 149 (Polychromatic418967fa.accept_11_1_5_6_1_397 12 104 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 104 149 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 104 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 104 149 (accept_3_2 10 104 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 104 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 104 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 104 149
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 104 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 104 149 (accept_3_2 7 104 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  104 149 (Polychromatic418967fa.accept_17_6_2_13_1_3051 6 104 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 104 149 (Polychromatic418967fa.accept_10_5_4_9_1_420 5 104 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 104 149 (accept_3_2 4 104 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 104 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 104 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 104 149
  (Polychromatic418967fa.accept_12_2_8_5_1_408 2 104 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 104 149 (accept_3_2 1 104 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  149)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 103 149 (Eq.refl Bool.true) (allA_of_3_0 47 103 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 102 149 (Eq.refl Bool.true) (allA_succ_of_accept 47 102 149
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 102 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 102 149 (accept_3_2 46 102 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 102 149 (Polychromatic418967fa.accept_18_9_12_5_1_864 45 102 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 102 149 (Polychromatic418967fa.accept_9_8_3_5_1_241 44 102 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 102 149 (accept_3_2 43 102 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 102 149 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 102 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 102 149
  (Polychromatic418967fa.accept_7_6_4_2_1_236 41 102 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 102 149 (accept_3_2 40 102 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 102 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 102 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 102 149 (Polychromatic418967fa.accept_9_2_3_5_1_60 38 102 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 102 149 (accept_3_2 37 102 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 102 149 (Polychromatic418967fa.accept_16_4_6_5_1_2245 36 102 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 102 149
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 102 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 102 149 (accept_3_2 34 102 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 102 149 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 102 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 102 149 (Polychromatic418967fa.accept_15_2_12_14_1_1709 32 102 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 102 149 (accept_3_2 31 102 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 102 149 (Polychromatic418967fa.accept_11_8_3_6_1_1855 30 102
  149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 102 149
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 102 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 102 149 (accept_3_2 28 102 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 102 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 102 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 102 149 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 102 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 102 149 (accept_3_2 25 102 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 102 149 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 102 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 102 149
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 102 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 102 149 (accept_3_2 22 102 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 102 149 (Polychromatic418967fa.accept_10_1_2_9_1_152 21 102 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 102 149 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 102 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 102 149 (accept_3_2 19 102 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 102 149 (Polychromatic418967fa.accept_13_5_11_6_1_505 18 102 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 102 149
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 102 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 102 149 (accept_3_2 16 102 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 102 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 102 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 102 149 (Polychromatic418967fa.accept_24_14_6_5_1_7999 14 102 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 102 149 (accept_3_2 13 102 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 102 149 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 102 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 102 149
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 102 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 102 149 (accept_3_2 10 102 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  102 149 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 102 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 102 149 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 102 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 102 149 (accept_3_2 7 102 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 102 149 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 102 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 102 149
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 102 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 102 149 (accept_3_2 4 102 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  102 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 102 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 102 149 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 102 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 102 149 (accept_3_2 1 102 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 102 149)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 101 149 (Eq.refl
  Bool.true) (allA_succ_of_accept 48 101 149 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 101 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 101 149 (Polychromatic418967fa.accept_7_5_3_2_1_249
  47 101 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 101 149 (accept_3_2 46
  101 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 101 149
  (Polychromatic418967fa.accept_10_5_1_9_1_791 45 101 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 101 149 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 101 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 101 149 (accept_3_2 43 101 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 101 149 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 101 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 101 149 (Polychromatic418967fa.accept_7_6_3_2_1_461
  41 101 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 101 149 (accept_3_2 40
  101 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 101 149
  (Polychromatic418967fa.accept_9_3_2_5_1_234 39 101 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 101 149 (Polychromatic418967fa.accept_10_8_1_9_1_413 38 101 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 101 149 (accept_3_2 37 101 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 101 149 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 101 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 101 149 (Polychromatic418967fa.accept_9_8_2_5_1_237
  35 101 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 101 149 (accept_3_2 34
  101 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 101 149
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 101 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 101 149 (Polychromatic418967fa.accept_10_2_1_9_1_1248 32 101 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 101 149 (accept_3_2 31 101 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 101 149 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 101 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 101 149 (Polychromatic418967fa.accept_7_1_3_2_1_13 29
  101 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 101 149 (accept_3_2 28
  101 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 101 149
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 101 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 101 149 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 101 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 101 149 (accept_3_2 25 101 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 101 149 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 101 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 101 149
  (Polychromatic418967fa.accept_25_23_1_24_1_7998 23 101 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 101 149 (accept_3_2 22 101 149 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 101 149 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 101 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 101 149 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 101 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 101 149 (accept_3_2 19 101 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 101 149 (Polychromatic418967fa.accept_10_8_1_9_1_413
  18 101 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 101 149
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 101 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 101 149 (accept_3_2 16 101 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 101 149 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 101 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 101 149 (Polychromatic418967fa.accept_18_14_11_5_1_7967 14 101 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 101 149 (accept_3_2 13 101 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 101 149 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 101 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 101 149
  (Polychromatic418967fa.accept_19_11_6_16_1_3805 11 101 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 101 149 (accept_3_2 10 101 149 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 101 149 (Polychromatic418967fa.accept_13_9_10_6_1_1028 9 101 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 149 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 101 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 101 149 (accept_3_2 7 101 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 101 149 (Polychromatic418967fa.accept_7_6_3_2_1_461 6
  101 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 101 149
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 101 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 101 149 (accept_3_2 4 101 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  101 149 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 101 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 101 149 (Polychromatic418967fa.accept_10_2_1_9_1_1248 2 101 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 101 149 (accept_3_2 1 101 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 101 149))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 100 149
  (Eq.refl Bool.true) (allA_of_3_0 50 100 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 99 149 (Eq.refl
  Bool.true) (allA_succ_of_accept 50 99 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 99 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 99 149 (accept_3_2 49 99 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 99 149 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 99 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 99 149
  (Polychromatic418967fa.accept_19_9_4_16_1_2586 47 99 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 99 149 (accept_3_2 46 99 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  99 149 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 99 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 99 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 99 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 99 149 (accept_3_2 43 99 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 99 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 99 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 99 149
  (Polychromatic418967fa.accept_7_6_1_2_1_230 41 99 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 99 149 (accept_3_2 40 99 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  99 149 (Polychromatic418967fa.accept_19_1_4_16_1_7997 39 99 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 99 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 99 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 99 149 (accept_3_2 37 99 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 99 149 (Polychromatic418967fa.accept_14_8_1_9_1_2085 36 99 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 99 149
  (Polychromatic418967fa.accept_15_5_9_14_1_1724 35 99 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 99 149 (accept_3_2 34 99 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  99 149 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 99 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 99 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 99 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 149 (accept_3_2 31 99 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 99 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 99 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 149
  (Polychromatic418967fa.accept_19_10_4_16_1_7996 29 99 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 99 149 (accept_3_2 28 99 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  99 149 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 99 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 99 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 99 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 149 (accept_3_2 25 99 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 99 149 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 99 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 99 149
  (Polychromatic418967fa.accept_15_8_9_14_1_4577 23 99 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 99 149 (accept_3_2 22 99 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  99 149 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 99 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 99 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 99 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 99 149 (accept_3_2 19 99 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 99 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 99 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 149
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 99 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 99 149 (accept_3_2 16 99 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  99 149 (Polychromatic418967fa.accept_13_2_8_6_1_2390 15 99 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 99 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 99 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 149 (accept_3_2 13 99 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 99 149 (Polychromatic418967fa.accept_15_12_9_14_1_2635 12 99 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 99 149
  (Polychromatic418967fa.accept_13_11_8_6_1_1023 11 99 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 99 149 (accept_3_2 10 99 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  99 149 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 99 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 99 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 99 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 149 (accept_3_2 7 99 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 99 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 99 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 149
  (Polychromatic418967fa.accept_15_5_9_14_1_1724 5 99 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 99 149 (accept_3_2 4 99 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99
  149 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 99 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 99 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 99 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 149 (accept_3_2 1 99 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 99 149))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 98 149 (Eq.refl
  Bool.true) (allA_succ_of_accept 51 98 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 98 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 98 149 (Polychromatic418967fa.accept_15_5_8_14_1_432
  50 98 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 98 149 (accept_3_2 49
  98 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 98 149
  (Polychromatic418967fa.accept_9_3_8_5_1_65 48 98 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 98 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 98 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 98 149 (accept_3_2 46 98 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 98 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 98 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 98 149 (Polychromatic418967fa.accept_10_4_8_9_1_784
  44 98 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 98 149 (accept_3_2 43
  98 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 98 149
  (Polychromatic418967fa.accept_9_6_8_5_1_837 42 98 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 98 149 (Polychromatic418967fa.accept_10_1_8_9_1_787 41 98 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 98 149 (accept_3_2 40 98 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 98 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 98 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 98 149 (Polychromatic418967fa.accept_9_2_8_5_1_228 38
  98 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 98 149 (accept_3_2 37 98
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 98 149
  (Polychromatic418967fa.accept_15_6_8_14_1_4575 36 98 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 98 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 98 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 98 149 (accept_3_2 34 98 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 98 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 98 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 98 149 (Polychromatic418967fa.accept_12_8_2_5_1_844
  32 98 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 98 149 (accept_3_2 31
  98 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 98 149
  (Polychromatic418967fa.accept_9_3_8_5_1_65 30 98 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 98 149 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 98 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 98 149 (accept_3_2 28 98 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 98 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 98 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 98 149
  (Polychromatic418967fa.accept_22_4_10_17_1_3182 26 98 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 98 149 (accept_3_2 25 98 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  98 149 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 98 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 98 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 98 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 98 149 (accept_3_2 22 98 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 98 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 98 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 98 149
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 98 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 98 149 (accept_3_2 19 98 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  98 149 (Polychromatic418967fa.accept_19_18_3_16_1_7962 18 98 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 98 149 (Polychromatic418967fa.accept_10_7_8_9_1_785 17 98 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 98 149 (accept_3_2 16 98 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 98 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 98 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 98 149
  (Polychromatic418967fa.accept_10_4_8_9_1_784 14 98 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 98 149 (accept_3_2 13 98 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  98 149 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 98 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 98 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 98 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 98 149 (accept_3_2 10 98 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 98 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 98 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 98 149
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 98 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 98 149 (accept_3_2 7 98 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 98
  149 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 98 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 98 149 (Polychromatic418967fa.accept_11_5_10_6_1_793 5 98 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 98 149 (accept_3_2 4 98 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 98 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 98 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 98 149 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  98 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 98 149 (accept_3_2 1 98 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98 149))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 53 97 149 (Eq.refl Bool.true) (allA_of_3_0 53 97 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  54 96 149 (Eq.refl Bool.true) (allA_succ_of_accept 53 96 149 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 96 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 96 149 (accept_3_2 52 96 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 96 149 (Polychromatic418967fa.accept_13_12_5_6_1_1050
  51 96 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 96 149
  (Polychromatic418967fa.accept_13_11_5_6_1_519 50 96 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 96 149 (accept_3_2 49 96 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  96 149 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 96 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 96 149 (Polychromatic418967fa.accept_9_2_6_5_1_227 47 96 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 96 149 (accept_3_2 46 96 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 96 149 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 96 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 96 149
  (Polychromatic418967fa.accept_9_8_6_5_1_513 44 96 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 96 149 (accept_3_2 43 96 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  96 149 (Polychromatic418967fa.accept_13_3_5_6_1_3192 42 96 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 96 149 (Polychromatic418967fa.accept_17_7_11_13_1_2037 41 96 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 96 149 (accept_3_2 40 96 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 96 149 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 96 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 96 149
  (Polychromatic418967fa.accept_7_3_5_2_1_17 38 96 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 96 149 (accept_3_2 37 96 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  96 149 (Polychromatic418967fa.accept_11_3_8_6_1_788 36 96 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 96 149 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 96 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 96 149 (accept_3_2 34 96 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 96 149 (Polychromatic418967fa.accept_10_3_6_9_1_779 33 96 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 96 149
  (Polychromatic418967fa.accept_7_4_5_2_1_243 32 96 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 96 149 (accept_3_2 31 96 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  96 149 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 96 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 96 149 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 96 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 96 149 (accept_3_2 28 96 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 96 149 (Polychromatic418967fa.accept_13_1_5_6_1_1048 27 96 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 96 149
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 96 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 96 149 (accept_3_2 25 96 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  96 149 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 96 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 96 149 (Polychromatic418967fa.accept_10_3_6_9_1_779 23 96 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 96 149 (accept_3_2 22 96 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 96 149 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 96 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 96 149
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 96 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 96 149 (accept_3_2 19 96 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  96 149 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 96 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 96 149 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 96 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 96 149 (accept_3_2 16 96 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 96 149 (Polychromatic418967fa.accept_10_5_6_9_1_2235 15 96 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 96 149
  (Polychromatic418967fa.accept_11_3_8_6_1_788 14 96 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 96 149 (accept_3_2 13 96 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  96 149 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 96 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 96 149 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 96 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 96 149 (accept_3_2 10 96 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 96 149 (Polychromatic418967fa.accept_15_9_6_14_1_2627 9 96 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 96 149
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 96 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 96 149 (accept_3_2 7 96 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 96
  149 (Polychromatic418967fa.accept_17_6_11_13_1_4180 6 96 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 96 149 (Polychromatic418967fa.accept_10_5_6_9_1_2235 5 96 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 96 149 (accept_3_2 4 96 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 96 149 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 96 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 96 149
  (Polychromatic418967fa.accept_9_2_6_5_1_227 2 96 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 96 149 (accept_3_2 1 96 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  149)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 95 149 (Eq.refl Bool.true)
  (allA_succ_of_accept 54 95 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 95 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 149 (Polychromatic418967fa.accept_15_8_5_14_1_986 53 95 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 95 149 (accept_3_2 52 95 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 95 149 (Polychromatic418967fa.accept_10_1_5_9_1_157
  51 95 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 95 149
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 95 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 95 149 (accept_3_2 49 95 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  95 149 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 95 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 95 149 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 95 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 95 149 (accept_3_2 46 95 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 95 149 (Polychromatic418967fa.accept_11_1_7_6_1_378 45 95 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 95 149
  (Polychromatic418967fa.accept_10_4_5_9_1_1231 44 95 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 95 149 (accept_3_2 43 95 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  95 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 95 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 95 149 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 95 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 95 149 (accept_3_2 40 95 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 95 149 (Polychromatic418967fa.accept_15_9_5_14_1_973 39 95 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 95 149
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 95 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 95 149 (accept_3_2 37 95 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  95 149 (Polychromatic418967fa.accept_10_6_5_9_1_1233 36 95 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 95 149 (Polychromatic418967fa.accept_13_9_4_6_1_1005 35 95 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 95 149 (accept_3_2 34 95 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 95 149 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 95 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 95 149
  (Polychromatic418967fa.accept_15_2_5_14_1_61 32 95 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 95 149 (accept_3_2 31 95 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  95 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 95 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 95 149 (Polychromatic418967fa.accept_23_6_3_11_1_7995 29 95 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 95 149 (accept_3_2 28 95 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 95 149 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 95 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 95 149
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 95 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 95 149 (accept_3_2 25 95 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  95 149 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 95 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 95 149 (Polychromatic418967fa.accept_11_1_7_6_1_378 23 95 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 95 149 (accept_3_2 22 95 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 95 149 (Polychromatic418967fa.accept_10_1_5_9_1_157 21 95 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 95 149
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 95 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 95 149 (accept_3_2 19 95 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  95 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 95 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 95 149 (Polychromatic418967fa.accept_15_2_5_14_1_61 17 95 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 95 149 (accept_3_2 16 95 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 95 149 (Polychromatic418967fa.accept_13_2_4_6_1_2356 15 95 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 95 149
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 95 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 95 149 (accept_3_2 13 95 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  95 149 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 95 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 95 149 (Polychromatic418967fa.accept_10_1_5_9_1_157 11 95 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 95 149 (accept_3_2 10 95 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 95 149 (Polychromatic418967fa.accept_13_9_4_6_1_1005 9 95 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 95 149
  (Polychromatic418967fa.accept_15_8_5_14_1_986 8 95 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 95 149 (accept_3_2 7 95 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 95
  149 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 95 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 95 149 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 95 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 95 149 (accept_3_2 4 95 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 95 149 (Polychromatic418967fa.accept_17_3_10_13_1_2021 3 95 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 95 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 95
  149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 149 (accept_3_2 1 95 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 95 149)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 56 94 149 (Eq.refl Bool.true) (allA_of_3_0 56 94 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  57 93 149 (Eq.refl Bool.true) (allA_succ_of_accept 56 93 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 93 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 93 149 (accept_3_2 55 93 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 93 149 (Polychromatic418967fa.accept_10_4_3_9_1_1262
  54 93 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 93 149
  (Polychromatic418967fa.accept_9_8_3_5_1_241 53 93 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 93 149 (accept_3_2 52 93 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  93 149 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 93 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 93 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 93 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 93 149 (accept_3_2 49 93 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 93 149 (Polychromatic418967fa.accept_13_9_2_6_1_514 48 93 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 93 149
  (Polychromatic418967fa.accept_9_2_3_5_1_60 47 93 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 93 149 (accept_3_2 46 93 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  93 149 (Polychromatic418967fa.accept_11_1_5_6_1_397 45 93 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 93 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 93 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 93 149 (accept_3_2 43 93 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 93 149 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 93 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 93 149
  (Polychromatic418967fa.accept_15_11_3_14_1_971 41 93 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 93 149 (accept_3_2 40 93 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  93 149 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 93 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 93 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 93 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 93 149 (accept_3_2 37 93 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 93 149 (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 93 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 93 149
  (Polychromatic418967fa.accept_9_8_3_5_1_241 35 93 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 93 149 (accept_3_2 34 93 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  93 149 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 93 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 93 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 93 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 93 149 (accept_3_2 31 93 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 93 149 (Polychromatic418967fa.accept_13_4_2_6_1_1043 30 93 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 93 149
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 93 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 93 149 (accept_3_2 28 93 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  93 149 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 93 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 93 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 93 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 93 149 (accept_3_2 25 93 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 93 149 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 93 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 93 149
  (Polychromatic418967fa.accept_11_1_5_6_1_397 23 93 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 93 149 (accept_3_2 22 93 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  93 149 (Polychromatic418967fa.accept_11_10_5_6_1_1842 21 93 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 93 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 93 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 149 (accept_3_2 19 93 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 93 149 (Polychromatic418967fa.accept_16_2_13_5_1_2257 18 93 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 149
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 93 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 93 149 (accept_3_2 16 93 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  93 149 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 93 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 93 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 93 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 149 (accept_3_2 13 93 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 93 149 (Polychromatic418967fa.accept_11_1_5_6_1_397 12 93 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 149
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 93 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 93 149 (accept_3_2 10 93 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  93 149 (Polychromatic418967fa.accept_13_9_2_6_1_514 9 93 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 93 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 93 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 149 (accept_3_2 7 93 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 93 149 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 93 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 149
  (Polychromatic418967fa.accept_17_5_8_13_1_7994 5 93 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 93 149 (accept_3_2 4 93 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93
  149 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 93 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 93 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 93 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 149 (accept_3_2 1 93 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 93 149))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 92 149 (Eq.refl
  Bool.true) (allA_succ_of_accept 57 92 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 92 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 92 149 (Polychromatic418967fa.accept_16_8_12_5_1_200
  56 92 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 92 149 (accept_3_2 55
  92 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 92 149
  (Polychromatic418967fa.accept_13_2_1_6_1_2365 54 92 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 92 149 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 92 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 92 149 (accept_3_2 52 92 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 92 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 92 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 92 149 (Polychromatic418967fa.accept_12_2_8_5_1_408
  50 92 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 92 149 (accept_3_2 49
  92 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 92 149
  (Polychromatic418967fa.accept_7_6_1_2_1_230 48 92 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 92 149 (Polychromatic418967fa.accept_10_7_2_9_1_775 47 92 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 92 149 (accept_3_2 46 92 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 92 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 92 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 92 149 (Polychromatic418967fa.accept_9_8_2_5_1_237 44
  92 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 92 149 (accept_3_2 43 92
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 92 149
  (Polychromatic418967fa.accept_9_6_2_5_1_506 42 92 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 92 149 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 92 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 92 149 (accept_3_2 40 92 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 92 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 92 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 92 149 (Polychromatic418967fa.accept_7_3_1_2_1_247 38
  92 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 92 149 (accept_3_2 37 92
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 92 149
  (Polychromatic418967fa.accept_16_4_12_5_1_2287 36 92 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 92 149 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 92 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 92 149 (accept_3_2 34 92 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 92 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 92 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 92 149
  (Polychromatic418967fa.accept_22_10_4_17_1_7993 32 92 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 92 149 (accept_3_2 31 92 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  92 149 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 92 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 92 149 (Polychromatic418967fa.accept_13_3_1_6_1_509 29 92 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 92 149 (accept_3_2 28 92 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 92 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 92 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 92 149
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 92 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 92 149 (accept_3_2 25 92 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  92 149 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 92 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 92 149 (Polychromatic418967fa.accept_16_7_12_5_1_734 23 92 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 92 149 (accept_3_2 22 92 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 92 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 92 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 92 149
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 92 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 92 149 (accept_3_2 19 92 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  92 149 (Polychromatic418967fa.accept_13_5_1_6_1_2367 18 92 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 92 149 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 92 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 92 149 (accept_3_2 16 92 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 92 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 92 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 92 149
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 92 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 92 149 (accept_3_2 13 92 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  92 149 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 92 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 92 149 (Polychromatic418967fa.accept_10_1_2_9_1_152 11 92 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 92 149 (accept_3_2 10 92 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 92 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 92 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 92 149
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 92 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 92 149 (accept_3_2 7 92 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 92
  149 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 92 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 92 149 (Polychromatic418967fa.accept_13_5_1_6_1_2367 5 92 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 92 149 (accept_3_2 4 92 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 92 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 92 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 92 149 (Polychromatic418967fa.accept_11_2_4_6_1_2412 2
  92 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 149 (accept_3_2 1 92 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92 149))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 59 91 149 (Eq.refl Bool.true) (allA_of_3_0 59 91 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  60 90 149 (Eq.refl Bool.true) (allA_succ_of_accept 59 90 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 90 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 90 149 (accept_3_2 58 90 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 90 149 (Polychromatic418967fa.accept_7_1_6_2_1_18 57
  90 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 90 149
  (Polychromatic418967fa.accept_19_18_14_16_1_2601 56 90 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 90 149 (accept_3_2 55 90 149 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 90 149 (Polychromatic418967fa.accept_13_2_12_6_1_2394 54 90 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 90 149 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 90 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 90 149 (accept_3_2 52 90 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 90 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 51
  90 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 90 149
  (Polychromatic418967fa.accept_7_1_6_2_1_18 50 90 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 90 149 (accept_3_2 49 90 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  90 149 (Polychromatic418967fa.accept_11_4_2_6_1_389 48 90 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 90 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 90 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 90 149 (accept_3_2 46 90 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 90 149 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 90 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 90 149
  (Polychromatic418967fa.accept_13_5_12_6_1_508 44 90 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 90 149 (accept_3_2 43 90 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  90 149 (Polychromatic418967fa.accept_17_8_5_13_1_4158 42 90 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 90 149 (Polychromatic418967fa.accept_13_2_12_6_1_2394 41 90 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 90 149 (accept_3_2 40 90 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 90 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 90 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 90 149
  (Polychromatic418967fa.accept_7_3_6_2_1_90 38 90 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 90 149 (accept_3_2 37 90 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  90 149 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 90 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 90 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 90 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 90 149 (accept_3_2 34 90 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 90 149 (Polychromatic418967fa.accept_13_7_12_6_1_1039 33 90 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 90 149
  (Polychromatic418967fa.accept_7_4_6_2_1_451 32 90 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 90 149 (accept_3_2 31 90 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  90 149 (Polychromatic418967fa.accept_16_14_10_5_1_1393 30 90 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 90 149 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 90 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 90 149 (accept_3_2 28 90 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 90 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 90 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 90 149
  (Polychromatic418967fa.accept_11_4_2_6_1_389 26 90 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 90 149 (accept_3_2 25 90 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  90 149 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 90 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 90 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 90 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 90 149 (accept_3_2 22 90 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 90 149 (Polychromatic418967fa.accept_19_2_14_16_1_7992 21 90 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 90 149
  (Polychromatic418967fa.accept_13_7_12_6_1_1039 20 90 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 90 149 (accept_3_2 19 90 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  90 149 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 90 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 90 149 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 90 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 90 149 (accept_3_2 16 90 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 90 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 90 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 90 149
  (Polychromatic418967fa.accept_16_14_10_5_1_1393 14 90 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 90 149 (accept_3_2 13 90 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  90 149 (Polychromatic418967fa.accept_16_12_10_5_1_5457 12 90 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 90 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 90 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 90 149 (accept_3_2 10 90 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 90 149 (Polychromatic418967fa.accept_17_9_5_13_1_2033 9 90 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 90 149
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 90 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 90 149 (accept_3_2 7 90 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 90
  149 (Polychromatic418967fa.accept_20_6_10_9_1_3486 6 90 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 90 149 (Polychromatic418967fa.accept_13_5_12_6_1_508 5 90 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 90 149 (accept_3_2 4 90 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 90 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 90 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 90 149
  (Polychromatic418967fa.accept_13_2_12_6_1_2394 2 90 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 90 149 (accept_3_2 1 90 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  149)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 89 149 (Eq.refl Bool.true)
  (allA_succ_of_accept 60 89 149 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 89 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 149 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 89 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 89 149 (accept_3_2 58 89 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 89 149 (Polychromatic418967fa.accept_9_3_8_5_1_65 57
  89 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 89 149
  (Polychromatic418967fa.accept_9_2_8_5_1_228 56 89 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 89 149 (accept_3_2 55 89 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  89 149 (Polychromatic418967fa.accept_17_3_4_13_1_2030 54 89 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 89 149 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 89 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 89 149 (accept_3_2 52 89 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 89 149 (Polychromatic418967fa.accept_9_6_8_5_1_837 51 89 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 89 149
  (Polychromatic418967fa.accept_19_12_13_16_1_6514 50 89 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 89 149 (accept_3_2 49 89 149 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 89 149 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 89 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 149 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 89 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 89 149 (accept_3_2 46 89 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 89 149 (Polychromatic418967fa.accept_7_3_5_2_1_17 45
  89 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 89 149
  (Polychromatic418967fa.accept_8_4_1_5_1_186 44 89 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 89 149 (accept_3_2 43 89 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  89 149 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 89 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 89 149 (Polychromatic418967fa.accept_19_3_13_16_1_6532 41 89 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 89 149 (accept_3_2 40 89 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 89 149 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 89 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 89 149
  (Polychromatic418967fa.accept_7_3_5_2_1_17 38 89 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 89 149 (accept_3_2 37 89 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  89 149 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 89 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 89 149 (Polychromatic418967fa.accept_14_7_5_9_1_2911 35 89 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 89 149 (accept_3_2 34 89 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 89 149 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 89 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 89 149
  (Polychromatic418967fa.accept_7_4_5_2_1_243 32 89 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 89 149 (accept_3_2 31 89 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  89 149 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 89 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 89 149 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 89 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 89 149 (accept_3_2 28 89 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 89 149 (Polychromatic418967fa.accept_11_5_1_6_1_774 27 89 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 89 149
  (Polychromatic418967fa.accept_17_9_4_13_1_3057 26 89 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 89 149 (accept_3_2 25 89 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  89 149 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 89 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 89 149 (Polychromatic418967fa.accept_24_23_17_5_1_7991 23 89 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 89 149 (accept_3_2 22 89 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 89 149 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 89 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 89 149
  (Polychromatic418967fa.accept_8_4_1_5_1_186 20 89 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 89 149 (accept_3_2 19 89 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  89 149 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 89 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 89 149 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 89 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 89 149 (accept_3_2 16 89 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 89 149 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 89 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 89 149
  (Polychromatic418967fa.accept_16_14_9_5_1_4388 14 89 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 89 149 (accept_3_2 13 89 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  89 149 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 89 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 89 149 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 89 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 89 149 (accept_3_2 10 89 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 89 149 (Polychromatic418967fa.accept_17_9_4_13_1_3057 9 89 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 89 149
  (Polychromatic418967fa.accept_13_8_11_6_1_1035 8 89 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 89 149 (accept_3_2 7 89 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 89
  149 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 89 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 89 149 (Polychromatic418967fa.accept_11_5_1_6_1_774 5 89 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 89 149 (accept_3_2 4 89 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 89 149 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 89 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 89 149 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  89 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 149 (accept_3_2 1 89 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 89 149)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 62 88 149 (Eq.refl Bool.true) (allA_of_3_0 62 88 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  63 87 149 (Eq.refl Bool.true) (allA_succ_of_accept 62 87 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 87 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 87 149 (accept_3_2 61 87 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 87 149 (Polychromatic418967fa.accept_11_5_10_6_1_793
  60 87 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 87 149
  (Polychromatic418967fa.accept_13_7_9_6_1_148 59 87 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 87 149 (accept_3_2 58 87 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  87 149 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 87 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 87 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 87 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 87 149 (accept_3_2 55 87 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 87 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 87 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 87 149
  (Polychromatic418967fa.accept_9_8_6_5_1_513 53 87 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 87 149 (accept_3_2 52 87 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  87 149 (Polychromatic418967fa.accept_19_13_11_16_1_1473 51 87 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 87 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 87 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 149 (accept_3_2 49 87 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 87 149 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 87 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 87 149
  (Polychromatic418967fa.accept_7_5_3_2_1_249 47 87 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 87 149 (accept_3_2 46 87 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  87 149 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 87 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 87 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 87 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 87 149 (accept_3_2 43 87 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 87 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 87 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 87 149
  (Polychromatic418967fa.accept_7_6_3_2_1_461 41 87 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 87 149 (accept_3_2 40 87 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  87 149 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 87 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 87 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 87 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 87 149 (accept_3_2 37 87 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 87 149 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 87 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 87 149
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 87 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 87 149 (accept_3_2 34 87 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  87 149 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 87 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 87 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 87 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 149 (accept_3_2 31 87 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 87 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 87 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 149
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 87 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 87 149 (accept_3_2 28 87 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  87 149 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 87 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 87 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 87 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 149 (accept_3_2 25 87 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 87 149 (Polychromatic418967fa.accept_15_9_12_14_1_963 24 87 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 149
  (Polychromatic418967fa.accept_13_10_9_6_1_1026 23 87 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 87 149 (accept_3_2 22 87 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  87 149 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 87 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 87 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 87 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 149 (accept_3_2 19 87 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 87 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 87 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 149
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 87 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 87 149 (accept_3_2 16 87 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  87 149 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 87 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 87 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 87 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 149 (accept_3_2 13 87 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 87 149 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 87 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 149
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 87 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 87 149 (accept_3_2 10 87 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  87 149 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 87 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 87 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 87 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 149 (accept_3_2 7 87 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 87 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 87 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 149
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 87 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 87 149 (accept_3_2 4 87 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87
  149 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 87 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 87 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 87 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 149 (accept_3_2 1 87 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 87 149))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 86 149
  (Eq.refl Bool.true) (allA_succ_of_accept 63 86 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 86 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 86 149
  (Polychromatic418967fa.accept_18_8_14_5_1_2778 62 86 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 86 149 (accept_3_2 61 86 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  86 149 (Polychromatic418967fa.accept_14_4_2_9_1_2092 60 86 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 86 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 86 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 86 149 (accept_3_2 58 86 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 86 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 86 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 86 149
  (Polychromatic418967fa.accept_12_8_2_5_1_844 56 86 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 86 149 (accept_3_2 55 86 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  86 149 (Polychromatic418967fa.accept_13_2_8_6_1_2390 54 86 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 86 149 (Polychromatic418967fa.accept_10_3_6_9_1_779 53 86 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 86 149 (accept_3_2 52 86 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 86 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 86 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 86 149
  (Polychromatic418967fa.accept_13_11_8_6_1_1023 50 86 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 86 149 (accept_3_2 49 86 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  86 149 (Polychromatic418967fa.accept_15_3_11_14_1_1705 48 86 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 86 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 86 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 86 149 (accept_3_2 46 86 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 86 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 86 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 86 149
  (Polychromatic418967fa.accept_12_8_2_5_1_844 44 86 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 86 149 (accept_3_2 43 86 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  86 149 (Polychromatic418967fa.accept_15_12_11_14_1_3464 42 86 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 86 149 (Polychromatic418967fa.accept_13_2_8_6_1_2390 41 86 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 86 149 (accept_3_2 40 86 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 86 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 86 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 86 149
  (Polychromatic418967fa.accept_23_15_17_11_1_7990 38 86 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 86 149 (accept_3_2 37 86 149 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 86 149 (Polychromatic418967fa.accept_11_3_9_6_1_105 36 86 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 86 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 86 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 86 149 (accept_3_2 34 86 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 86 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 33
  86 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 86 149
  (Polychromatic418967fa.accept_12_8_2_5_1_844 32 86 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 86 149 (accept_3_2 31 86 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  86 149 (Polychromatic418967fa.accept_20_10_6_9_1_4989 30 86 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 86 149 (Polychromatic418967fa.accept_17_12_1_13_1_6672 29 86 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 86 149 (accept_3_2 28 86 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 86 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 86 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 86 149
  (Polychromatic418967fa.accept_18_8_14_5_1_2778 26 86 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 86 149 (accept_3_2 25 86 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  86 149 (Polychromatic418967fa.accept_13_11_8_6_1_1023 24 86 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 86 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 86 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 86 149 (accept_3_2 22 86 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 86 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 86 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 86 149
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 86 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 86 149 (accept_3_2 19 86 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  86 149 (Polychromatic418967fa.accept_14_4_2_9_1_2092 18 86 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 86 149 (Polychromatic418967fa.accept_16_1_6_5_1_4385 17 86 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 86 149 (accept_3_2 16 86 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 86 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 86 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 86 149
  (Polychromatic418967fa.accept_11_3_9_6_1_105 14 86 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 86 149 (accept_3_2 13 86 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  86 149 (Polychromatic418967fa.accept_15_12_11_14_1_3464 12 86 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 86 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 86 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 86 149 (accept_3_2 10 86 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 86 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 86 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 149
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 86 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 86 149 (accept_3_2 7 86 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86
  149 (Polychromatic418967fa.accept_19_6_10_16_1_7989 6 86 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 86 149 (Polychromatic418967fa.accept_10_5_6_9_1_2235 5 86 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 86 149 (accept_3_2 4 86 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 86 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 86 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 86 149
  (Polychromatic418967fa.accept_13_2_8_6_1_2390 2 86 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 86 149 (accept_3_2 1 86 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  149)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 85 149 (Eq.refl Bool.true)
  (allA_of_3_0 65 85 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 66 84 149 (Eq.refl Bool.true)
  (allA_succ_of_accept 65 84 149 (Polychromatic418967fa.accept_8_1_4_5_1_48 65 84 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 84 149 (accept_3_2 64 84 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 84 149 (Polychromatic418967fa.accept_10_3_4_9_1_15 63 84 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 84 149 (Polychromatic418967fa.accept_9_8_3_5_1_241 62
  84 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 84 149 (accept_3_2 61 84
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 84 149
  (Polychromatic418967fa.accept_9_6_3_5_1_240 60 84 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 84 149 (Polychromatic418967fa.accept_20_19_4_9_1_5025 59 84 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 84 149 (accept_3_2 58 84 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 84 149 (Polychromatic418967fa.accept_8_1_4_5_1_48 57 84 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 84 149 (Polychromatic418967fa.accept_9_2_3_5_1_60 56
  84 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 84 149 (accept_3_2 55 84
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 84 149
  (Polychromatic418967fa.accept_16_6_4_5_1_2272 54 84 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 84 149 (Polychromatic418967fa.accept_9_8_3_5_1_241 53 84 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 84 149 (accept_3_2 52 84 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 84 149 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 84 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 84 149 (Polychromatic418967fa.accept_15_5_9_14_1_1724
  50 84 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 84 149 (accept_3_2 49
  84 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 84 149
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 48 84 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 84 149 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 84 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 84 149 (accept_3_2 46 84 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 84 149 (Polychromatic418967fa.accept_10_5_4_9_1_420 45 84 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 84 149 (Polychromatic418967fa.accept_9_8_3_5_1_241 44
  84 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 84 149 (accept_3_2 43 84
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 84 149
  (Polychromatic418967fa.accept_9_6_3_5_1_240 42 84 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 84 149 (Polychromatic418967fa.accept_8_1_4_5_1_48 41 84 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 84 149 (accept_3_2 40 84 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 84 149 (Polychromatic418967fa.accept_19_1_8_16_1_6488 39 84 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 84 149
  (Polychromatic418967fa.accept_9_2_3_5_1_60 38 84 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 84 149 (accept_3_2 37 84 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  84 149 (Polychromatic418967fa.accept_15_6_9_14_1_3457 36 84 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 84 149 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 84 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 84 149 (accept_3_2 34 84 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 84 149 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 84 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 84 149
  (Polychromatic418967fa.accept_22_10_18_17_1_1830 32 84 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 84 149 (accept_3_2 31 84 149 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 84 149 (Polychromatic418967fa.accept_19_11_8_16_1_7988 30 84 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 84 149 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 84 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 84 149 (accept_3_2 28 84 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 84 149
  (Polychromatic418967fa.accept_15_12_9_14_1_2635 27 84 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 84 149 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 84 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 84 149 (accept_3_2 25 84 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 84 149 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 84 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 84 149 (Polychromatic418967fa.accept_10_3_4_9_1_15 23
  84 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 84 149 (accept_3_2 22 84
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 84 149
  (Polychromatic418967fa.accept_15_6_9_14_1_3457 21 84 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 84 149 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 84 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 149 (accept_3_2 19 84 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 84 149 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 84 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 84 149 (Polychromatic418967fa.accept_8_1_4_5_1_48 17
  84 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 84 149 (accept_3_2 16 84
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 84 149
  (Polychromatic418967fa.accept_9_6_3_5_1_240 15 84 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 84 149 (Polychromatic418967fa.accept_20_14_4_9_1_2249 14 84 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 149 (accept_3_2 13 84 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 84 149 (Polychromatic418967fa.accept_11_1_7_6_1_378 12 84 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 84 149 (Polychromatic418967fa.accept_9_2_3_5_1_60 11
  84 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 84 149 (accept_3_2 10 84
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 84 149 (Polychromatic418967fa.accept_8_1_4_5_1_48
  9 84 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 84 149
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 84 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 84 149 (accept_3_2 7 84 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 84
  149 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 84 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 84 149 (Polychromatic418967fa.accept_10_5_4_9_1_420 5 84 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 84 149 (accept_3_2 4 84 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 84 149 (Polychromatic418967fa.accept_10_3_4_9_1_15 3 84 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 84 149 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 84
  149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 149 (accept_3_2 1 84 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  149)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 83 149 (Eq.refl Bool.true)
  (allA_succ_of_accept 66 83 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 83 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 149 (Polychromatic418967fa.accept_15_5_8_14_1_432 65 83 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 83 149 (accept_3_2 64 83 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 83 149 (Polychromatic418967fa.accept_13_11_5_6_1_519
  63 83 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 83 149
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 83 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 83 149 (accept_3_2 61 83 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  83 149 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 83 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 83 149 (Polychromatic418967fa.accept_7_3_6_2_1_90 59 83 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 83 149 (accept_3_2 58 83 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 83 149 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 83 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 83 149
  (Polychromatic418967fa.accept_10_6_3_9_1_1207 56 83 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 83 149 (accept_3_2 55 83 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  83 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 83 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 83 149 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 83 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 83 149 (accept_3_2 52 83 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 83 149 (Polychromatic418967fa.accept_9_6_2_5_1_506 51 83 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 83 149
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 83 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 83 149 (accept_3_2 49 83 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  83 149 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 83 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 83 149 (Polychromatic418967fa.accept_19_9_7_16_1_2591 47 83 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 83 149 (accept_3_2 46 83 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 83 149 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 83 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 83 149
  (Polychromatic418967fa.accept_9_8_2_5_1_237 44 83 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 83 149 (accept_3_2 43 83 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  83 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 83 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 83 149 (Polychromatic418967fa.accept_24_17_11_5_1_7987 41 83 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 83 149 (accept_3_2 40 83 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 83 149 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 83 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 83 149
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 83 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 83 149 (accept_3_2 37 83 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  83 149 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 83 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 83 149 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 83 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 83 149 (accept_3_2 34 83 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 83 149 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 83 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 83 149
  (Polychromatic418967fa.accept_7_4_6_2_1_451 32 83 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 83 149 (accept_3_2 31 83 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  83 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 83 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 83 149 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 83 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 83 149 (accept_3_2 28 83 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 83 149 (Polychromatic418967fa.accept_13_1_5_6_1_1048 27 83 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 83 149
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 83 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 83 149 (accept_3_2 25 83 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  83 149 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 83 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 83 149 (Polychromatic418967fa.accept_13_10_5_6_1_1671 23 83 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 83 149 (accept_3_2 22 83 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 83 149 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 83 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 83 149
  (Polychromatic418967fa.accept_15_5_8_14_1_432 20 83 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 83 149 (accept_3_2 19 83 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  83 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 83 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 83 149 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 83 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 83 149 (accept_3_2 16 83 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 83 149 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 83 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 83 149
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 83 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 83 149 (accept_3_2 13 83 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  83 149 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 83 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 83 149 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 83 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 83 149 (accept_3_2 10 83 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 83 149 (Polychromatic418967fa.accept_15_9_8_14_1_1699 9 83 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 83 149
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 83 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 83 149 (accept_3_2 7 83 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 83
  149 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 83 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 83 149 (Polychromatic418967fa.accept_15_5_8_14_1_432 5 83 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 83 149 (accept_3_2 4 83 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 83 149 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 83 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 83 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 83
  149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 149 (accept_3_2 1 83 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 83
  149))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 82 149 (Eq.refl Bool.true)
  (allA_of_3_0 68 82 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 69 81 149 (Eq.refl Bool.true)
  (allA_succ_of_accept 68 81 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 81 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 81 149 (accept_3_2 67 81 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 81 149 (Polychromatic418967fa.accept_13_1_3_6_1_158 66 81 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 149 (Polychromatic418967fa.accept_10_5_1_9_1_791
  65 81 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 149 (accept_3_2 64
  81 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 149
  (Polychromatic418967fa.accept_12_3_9_5_1_853 63 81 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 81 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 81 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 149 (accept_3_2 61 81 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 81 149 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 81 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 149 (Polychromatic418967fa.accept_19_2_5_16_1_7986
  59 81 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 149 (accept_3_2 58
  81 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 149
  (Polychromatic418967fa.accept_11_2_4_6_1_2412 57 81 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 81 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 81 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 149 (accept_3_2 55 81 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 81 149 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 81 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 149 (Polychromatic418967fa.accept_13_1_3_6_1_158
  53 81 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 149 (accept_3_2 52
  81 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 149
  (Polychromatic418967fa.accept_12_3_9_5_1_853 51 81 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 81 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 81 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 81 149 (accept_3_2 49 81 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 81 149 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 81 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 149 (Polychromatic418967fa.accept_7_5_4_2_1_235 47
  81 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 149 (accept_3_2 46 81
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 149
  (Polychromatic418967fa.accept_10_5_1_9_1_791 45 81 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 81 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 81 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 149 (accept_3_2 43 81 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 81 149 (Polychromatic418967fa.accept_10_2_1_9_1_1248 42 81 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 149 (Polychromatic418967fa.accept_7_6_4_2_1_236 41
  81 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 149 (accept_3_2 40 81
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 149
  (Polychromatic418967fa.accept_12_3_9_5_1_853 39 81 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 81 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 81 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 149 (accept_3_2 37 81 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 81 149 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 81 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 149 (Polychromatic418967fa.accept_10_5_1_9_1_791
  35 81 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 149 (accept_3_2 34
  81 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 149
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 81 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 81 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 81 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 149 (accept_3_2 31 81 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 81 149 (Polychromatic418967fa.accept_14_2_11_9_1_2925 30 81 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 149
  (Polychromatic418967fa.accept_16_13_1_5_1_5469 29 81 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 81 149 (accept_3_2 28 81 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  81 149 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 81 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 81 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 81 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 149 (accept_3_2 25 81 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 81 149 (Polychromatic418967fa.accept_11_2_4_6_1_2412 24 81 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 149
  (Polychromatic418967fa.accept_13_10_3_6_1_1003 23 81 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 149 (accept_3_2 22 81 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  81 149 (Polychromatic418967fa.accept_19_2_5_16_1_7986 21 81 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 81 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 81 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 149 (accept_3_2 19 81 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 81 149 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 81 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 149
  (Polychromatic418967fa.accept_24_17_9_5_1_7985 17 81 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 81 149 (accept_3_2 16 81 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  81 149 (Polychromatic418967fa.accept_10_5_1_9_1_791 15 81 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 81 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 81 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 149 (accept_3_2 13 81 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 81 149 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 81 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 149
  (Polychromatic418967fa.accept_19_11_5_16_1_1456 11 81 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 81 149 (accept_3_2 10 81 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  81 149 (Polychromatic418967fa.accept_13_9_3_6_1_1661 9 81 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 81 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 81 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 149 (accept_3_2 7 81 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 149 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 81 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 149
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 81 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 149 (accept_3_2 4 81 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81
  149 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 81 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 81 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 81 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 149 (accept_3_2 1 81 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 81 149))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 80
  149 (Eq.refl Bool.true) (allA_succ_of_accept 69 80 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 80 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 80 149
  (Polychromatic418967fa.accept_7_5_3_2_1_249 68 80 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 80 149 (accept_3_2 67 80 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  80 149 (Polychromatic418967fa.accept_9_3_8_5_1_65 66 80 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 80 149 (Polychromatic418967fa.accept_9_2_8_5_1_228 65 80 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 80 149 (accept_3_2 64 80 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 80 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 80 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 80 149
  (Polychromatic418967fa.accept_7_6_3_2_1_461 62 80 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 80 149 (accept_3_2 61 80 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  80 149 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 80 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 80 149 (Polychromatic418967fa.accept_19_2_4_16_1_7984 59 80 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 80 149 (accept_3_2 58 80 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 80 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 80 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 80 149
  (Polychromatic418967fa.accept_9_2_8_5_1_228 56 80 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 80 149 (accept_3_2 55 80 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  80 149 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 80 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 80 149 (Polychromatic418967fa.accept_11_9_3_6_1_797 53 80 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 80 149 (accept_3_2 52 80 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 80 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 80 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 80 149
  (Polychromatic418967fa.accept_7_1_3_2_1_13 50 80 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 80 149 (accept_3_2 49 80 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  80 149 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 80 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 80 149 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 80 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 80 149 (accept_3_2 46 80 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 80 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 80 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 80 149
  (Polychromatic418967fa.accept_25_19_5_24_1_7983 44 80 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 80 149 (accept_3_2 43 80 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  80 149 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 80 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 80 149 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 80 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 80 149 (accept_3_2 40 80 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 80 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 80 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 80 149
  (Polychromatic418967fa.accept_9_2_8_5_1_228 38 80 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 80 149 (accept_3_2 37 80 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  80 149 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 80 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 80 149 (Polychromatic418967fa.accept_13_9_2_6_1_514 35 80 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 80 149 (accept_3_2 34 80 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 80 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 80 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 80 149
  (Polychromatic418967fa.accept_15_2_5_14_1_61 32 80 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 80 149 (accept_3_2 31 80 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  80 149 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 80 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 80 149 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 80 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 80 149 (accept_3_2 28 80 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 80 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 80 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 80 149
  (Polychromatic418967fa.accept_7_5_3_2_1_249 26 80 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 80 149 (accept_3_2 25 80 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  80 149 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 80 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 80 149 (Polychromatic418967fa.accept_13_10_2_6_1_1044 23 80 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 80 149 (accept_3_2 22 80 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 80 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 80 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 80 149
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 80 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 80 149 (accept_3_2 19 80 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  80 149 (Polychromatic418967fa.accept_17_1_12_13_1_448 18 80 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 80 149 (Polychromatic418967fa.accept_13_4_2_6_1_1043 17 80 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 80 149 (accept_3_2 16 80 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 80 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 80 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 80 149
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 80 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 80 149 (accept_3_2 13 80 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  80 149 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 80 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 80 149 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 80 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 80 149 (accept_3_2 10 80 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 80 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 80 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 80 149
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 80 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 80 149 (accept_3_2 7 80 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 80
  149 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 80 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 80 149 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 80 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 80 149 (accept_3_2 4 80 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 80 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 80 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 80 149 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  80 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 80 149 (accept_3_2 1 80 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  149)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 79 149 (Eq.refl Bool.true)
  (allA_of_3_0 71 79 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 72 78 149 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 78 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 78 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 78 149 (accept_3_2 70 78 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 78 149 (Polychromatic418967fa.accept_7_6_1_2_1_230 69 78 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 78 149
  (Polychromatic418967fa.accept_19_11_2_16_1_3822 68 78 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 78 149 (accept_3_2 67 78 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  78 149 (Polychromatic418967fa.accept_7_3_1_2_1_247 66 78 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 78 149 (Polychromatic418967fa.accept_9_2_6_5_1_227 65 78 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 78 149 (accept_3_2 64 78 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 78 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 78 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 78 149
  (Polychromatic418967fa.accept_7_6_1_2_1_230 62 78 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 78 149 (accept_3_2 61 78 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  78 149 (Polychromatic418967fa.accept_11_5_1_6_1_774 60 78 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 78 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 78 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 78 149 (accept_3_2 58 78 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 78 149 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 78 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 78 149
  (Polychromatic418967fa.accept_9_2_6_5_1_227 56 78 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 78 149 (accept_3_2 55 78 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  78 149 (Polychromatic418967fa.accept_10_4_8_9_1_784 54 78 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 78 149 (Polychromatic418967fa.accept_9_8_6_5_1_513 53 78 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 78 149 (accept_3_2 52 78 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 78 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 78 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 78 149
  (Polychromatic418967fa.accept_21_8_15_2_1_4805 50 78 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 78 149 (accept_3_2 49 78 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  78 149 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 78 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 78 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 78 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 78 149 (accept_3_2 46 78 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 78 149 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 78 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 78 149
  (Polychromatic418967fa.accept_9_8_6_5_1_513 44 78 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 78 149 (accept_3_2 43 78 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  78 149 (Polychromatic418967fa.accept_16_10_14_5_1_5496 42 78 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 78 149 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 78 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 78 149 (accept_3_2 40 78 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 78 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 78 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 78 149
  (Polychromatic418967fa.accept_7_3_1_2_1_247 38 78 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 78 149 (accept_3_2 37 78 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  78 149 (Polychromatic418967fa.accept_19_17_2_16_1_7982 36 78 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 78 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 78 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 78 149 (accept_3_2 34 78 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 78 149 (Polychromatic418967fa.accept_18_15_6_5_1_3972 33 78 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 78 149
  (Polychromatic418967fa.accept_15_2_3_14_1_972 32 78 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 78 149 (accept_3_2 31 78 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  78 149 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 78 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 78 149 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 78 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 78 149 (accept_3_2 28 78 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 78 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 78 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 78 149
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 78 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 78 149 (accept_3_2 25 78 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  78 149 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 78 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 78 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 78 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 78 149 (accept_3_2 22 78 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 78 149 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 78 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 78 149
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 78 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 78 149 (accept_3_2 19 78 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  78 149 (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 78 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 78 149 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 78 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 78 149 (accept_3_2 16 78 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 78 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 78 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 78 149
  (Polychromatic418967fa.accept_10_4_8_9_1_784 14 78 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 78 149 (accept_3_2 13 78 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  78 149 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 78 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 78 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 78 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 78 149 (accept_3_2 10 78 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 78 149 (Polychromatic418967fa.accept_16_9_14_5_1_2239 9 78 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 78 149
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 78 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 78 149 (accept_3_2 7 78 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 78
  149 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 78 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 78 149 (Polychromatic418967fa.accept_11_5_1_6_1_774 5 78 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78 149 (accept_3_2 4 78 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 78 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 78 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 78 149 (Polychromatic418967fa.accept_9_2_6_5_1_227 2
  78 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 78 149 (accept_3_2 1 78 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  149)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 77 149 (Eq.refl Bool.true)
  (allA_succ_of_accept 72 77 149 (Polychromatic418967fa.accept_10_2_7_9_1_783 72 77 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 149 (Polychromatic418967fa.accept_21_8_14_2_1_7981 71 77
  149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 77 149 (accept_3_2 70 77 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 77 149 (Polychromatic418967fa.accept_21_6_14_2_1_7980
  69 77 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 77 149
  (Polychromatic418967fa.accept_10_8_7_9_1_425 68 77 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 77 149 (accept_3_2 67 77 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  77 149 (Polychromatic418967fa.accept_16_2_13_5_1_2257 66 77 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 77 149 (Polychromatic418967fa.accept_15_5_2_14_1_1693 65 77 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 77 149 (accept_3_2 64 77 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 77 149 (Polychromatic418967fa.accept_15_3_2_14_1_1713 63 77
  149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 77 149
  (Polychromatic418967fa.accept_10_2_7_9_1_783 62 77 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 77 149 (accept_3_2 61 77 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  77 149 (Polychromatic418967fa.accept_19_3_1_16_1_7947 60 77 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 77 149 (Polychromatic418967fa.accept_13_7_12_6_1_1039 59 77 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 77 149 (accept_3_2 58 77 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 77 149 (Polychromatic418967fa.accept_13_5_12_6_1_508 57 77 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 77 149
  (Polychromatic418967fa.accept_16_8_13_5_1_1395 56 77 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 77 149 (accept_3_2 55 77 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  77 149 (Polychromatic418967fa.accept_13_2_12_6_1_2394 54 77 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 77 149 (Polychromatic418967fa.accept_19_15_1_16_1_6499 53 77 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 77 149 (accept_3_2 52 77 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 77 149 (Polychromatic418967fa.accept_19_13_1_16_1_7979 51 77
  149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 77 149
  (Polychromatic418967fa.accept_15_5_2_14_1_1693 50 77 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 77 149 (accept_3_2 49 77 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  77 149 (Polychromatic418967fa.accept_10_8_7_9_1_425 48 77 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 77 149 (Polychromatic418967fa.accept_14_5_7_9_1_3828 47 77 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 77 149 (accept_3_2 46 77 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 77 149 (Polychromatic418967fa.accept_21_3_14_2_1_7978 45 77 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 77 149
  (Polychromatic418967fa.accept_13_5_12_6_1_508 44 77 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 77 149 (accept_3_2 43 77 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  77 149 (Polychromatic418967fa.accept_10_2_7_9_1_783 42 77 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 77 149 (Polychromatic418967fa.accept_13_2_12_6_1_2394 41 77 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 77 149 (accept_3_2 40 77 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 77 149 (Polychromatic418967fa.accept_17_5_9_13_1_1093 39 77
  149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 77 149
  (Polychromatic418967fa.accept_10_8_7_9_1_425 38 77 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 77 149 (accept_3_2 37 77 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  77 149 (Polychromatic418967fa.accept_13_10_12_6_1_991 36 77 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 77 149 (Polychromatic418967fa.accept_15_5_2_14_1_1693 35 77 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 77 149 (accept_3_2 34 77 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 77 149 (Polychromatic418967fa.accept_13_7_12_6_1_1039 33 77
  149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 77 149
  (Polychromatic418967fa.accept_10_2_7_9_1_783 32 77 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 77 149 (accept_3_2 31 77 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  77 149 (Polychromatic418967fa.accept_14_2_7_9_1_2937 30 77 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 77 149 (Polychromatic418967fa.accept_19_10_1_16_1_7977 29 77 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 77 149 (accept_3_2 28 77 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 77 149 (Polychromatic418967fa.accept_15_12_2_14_1_5659 27 77
  149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 77 149
  (Polychromatic418967fa.accept_14_12_7_9_1_726 26 77 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 77 149 (accept_3_2 25 77 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  77 149 (Polychromatic418967fa.accept_16_8_13_5_1_1395 24 77 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 77 149 (Polychromatic418967fa.accept_13_10_12_6_1_991 23 77 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 77 149 (accept_3_2 22 77 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 77 149 (Polychromatic418967fa.accept_17_4_9_13_1_2020 21 77
  149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 77 149
  (Polychromatic418967fa.accept_13_7_12_6_1_1039 20 77 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 77 149 (accept_3_2 19 77 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  77 149 (Polychromatic418967fa.accept_10_8_7_9_1_425 18 77 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 77 149 (Polychromatic418967fa.accept_16_1_13_5_1_2280 17 77 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 77 149 (accept_3_2 16 77 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 77 149 (Polychromatic418967fa.accept_13_2_12_6_1_2394 15 77
  149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 77 149
  (Polychromatic418967fa.accept_28_14_21_9_1_7976 14 77 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 77 149 (accept_3_2 13 77 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  77 149 (Polychromatic418967fa.accept_10_2_7_9_1_783 12 77 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 77 149 (Polychromatic418967fa.accept_21_11_14_2_1_6371 11 77 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 77 149 (accept_3_2 10 77 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 77 149 (Polychromatic418967fa.accept_16_9_13_5_1_2238 9 77 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 77 149
  (Polychromatic418967fa.accept_10_8_7_9_1_425 8 77 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 77 149 (accept_3_2 7 77 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 77
  149 (Polychromatic418967fa.accept_20_6_17_9_1_7975 6 77 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 77 149 (Polychromatic418967fa.accept_13_5_12_6_1_508 5 77 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 77 149 (accept_3_2 4 77 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 77 149 (Polychromatic418967fa.accept_15_3_2_14_1_1713 3 77 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 77 149
  (Polychromatic418967fa.accept_10_2_7_9_1_783 2 77 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 77 149 (accept_3_2 1 77 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 77
  149))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 76 149 (Eq.refl Bool.true)
  (allA_of_3_0 74 76 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 75 149 (allA_succ_of_accept 74 75 149
  (Polychromatic418967fa.accept_4_2_3_1_1_2 74 75 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 75 149 (accept_3_2 73 75 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  75 149 (Polychromatic418967fa.accept_16_8_11_5_1_3319 72 75 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 75 149 (Polychromatic418967fa.accept_9_8_3_5_1_241 71 75 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 75 149 (accept_3_2 70 75 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 149 (Polychromatic418967fa.accept_9_6_3_5_1_240 69 75 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 75 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 75 149 (accept_3_2 67 75 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  75 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 75 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 75 149 (Polychromatic418967fa.accept_9_2_3_5_1_60 65 75 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 149 (accept_3_2 64 75 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 149 (Polychromatic418967fa.accept_14_7_5_9_1_2911 63 75 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 149
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 75 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 149 (accept_3_2 61 75 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  75 149 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 75 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 75 149 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 75 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 149 (accept_3_2 58 75 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 149 (Polychromatic418967fa.accept_12_9_3_5_1_423 57 75 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 75 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 75 149 (accept_3_2 55 75 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  75 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 75 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 75 149 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 75 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 149 (accept_3_2 52 75 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 149 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 75 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 149
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 75 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 75 149 (accept_3_2 49 75 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  75 149 (Polychromatic418967fa.accept_13_9_10_6_1_1028 48 75 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 75 149 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 75 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 149 (accept_3_2 46 75 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 149 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 75 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 75 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 75 149 (accept_3_2 43 75 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  75 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 75 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 75 149 (Polychromatic418967fa.accept_10_1_5_9_1_157 41 75 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 149 (accept_3_2 40 75 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 149 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 75 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 149
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 75 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 75 149 (accept_3_2 37 75 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  75 149 (Polychromatic418967fa.accept_10_6_5_9_1_1233 36 75 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 75 149 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 75 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 149 (accept_3_2 34 75 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 149 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 75 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 75 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 149 (accept_3_2 31 75 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  75 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 75 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 75 149 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 75 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 149 (accept_3_2 28 75 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 149 (Polychromatic418967fa.accept_19_8_18_16_1_7937 27 75 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 149
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 75 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 75 149 (accept_3_2 25 75 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  75 149 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 75 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 75 149 (Polychromatic418967fa.accept_16_7_11_5_1_4402 23 75 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 149 (accept_3_2 22 75 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 149 (Polychromatic418967fa.accept_10_1_5_9_1_157 21 75 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 75 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 75 149 (accept_3_2 19 75 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  75 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 75 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 75 149 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 75 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 149 (accept_3_2 16 75 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 149 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 75 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 149
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 75 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 149 (accept_3_2 13 75 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  75 149 (Polychromatic418967fa.accept_13_12_10_6_1_3212 12 75 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 75 149 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 75 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 149 (accept_3_2 10 75 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 149 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 75 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 75 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 149 (accept_3_2 7 75 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75
  149 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 75 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 149 (Polychromatic418967fa.accept_13_5_10_6_1_2361 5 75 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 149 (accept_3_2 4 75 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 75 149 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 75 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 75
  149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 149 (accept_3_2 1 75 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  149))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 149 (allA_succ_of_accept
  73 74 149 (accept_3_2 73 74 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 74 149
  (Polychromatic418967fa.accept_13_7_9_6_1_148 72 74 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 74 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 74 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 74 149 (accept_3_2 70 74 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 74 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 74 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 74 149 (Polychromatic418967fa.accept_7_5_4_2_1_235 68
  74 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 74 149 (accept_3_2 67 74
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 74 149
  (Polychromatic418967fa.accept_9_3_2_5_1_234 66 74 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 74 149 (Polychromatic418967fa.accept_10_5_4_9_1_420 65 74 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 74 149 (accept_3_2 64 74 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 74 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 74 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 74 149 (Polychromatic418967fa.accept_7_6_4_2_1_236 62
  74 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 74 149 (accept_3_2 61 74
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 74 149
  (Polychromatic418967fa.accept_9_6_2_5_1_506 60 74 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 74 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 74 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 74 149 (accept_3_2 58 74 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 74 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 74 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 74 149 (Polychromatic418967fa.accept_12_8_2_5_1_844
  56 74 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 74 149 (accept_3_2 55
  74 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 74 149
  (Polychromatic418967fa.accept_7_5_4_2_1_235 54 74 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 74 149 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 74 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 74 149 (accept_3_2 52 74 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 74 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 74 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 74 149 (Polychromatic418967fa.accept_22_6_8_17_1_7974
  50 74 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 74 149 (accept_3_2 49
  74 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 74 149
  (Polychromatic418967fa.accept_7_6_4_2_1_236 48 74 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 74 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 74 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 74 149 (accept_3_2 46 74 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 74 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 74 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 74 149 (Polychromatic418967fa.accept_9_8_2_5_1_237 44
  74 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 74 149 (accept_3_2 43 74
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 74 149
  (Polychromatic418967fa.accept_9_6_2_5_1_506 42 74 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 74 149 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 74 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 74 149 (accept_3_2 40 74 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 74 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 74 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 74 149 (Polychromatic418967fa.accept_10_8_4_9_1_1229
  38 74 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 74 149 (accept_3_2 37
  74 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 74 149
  (Polychromatic418967fa.accept_11_3_8_6_1_788 36 74 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 74 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 74 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 74 149 (accept_3_2 34 74 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 74 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 74 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 74 149 (Polychromatic418967fa.accept_12_8_2_5_1_844
  32 74 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 74 149 (accept_3_2 31
  74 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 74 149
  (Polychromatic418967fa.accept_9_3_2_5_1_234 30 74 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 74 149 (Polychromatic418967fa.accept_13_3_9_6_1_502 29 74 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 74 149 (accept_3_2 28 74 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 74 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 74 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 74 149 (Polychromatic418967fa.accept_7_5_4_2_1_235 26
  74 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 74 149 (accept_3_2 25 74
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 74 149
  (Polychromatic418967fa.accept_9_6_2_5_1_506 24 74 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 74 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 74 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 74 149 (accept_3_2 22 74 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 74 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 74 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 74 149 (Polychromatic418967fa.accept_7_6_4_2_1_236 20
  74 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 74 149 (accept_3_2 19 74
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 74 149
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 74 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 74 149 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 74 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 74 149 (accept_3_2 16 74 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 74 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 74 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 74 149 (Polychromatic418967fa.accept_11_3_8_6_1_788
  14 74 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 74 149 (accept_3_2 13
  74 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 74 149
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 74 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 74 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 74 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 74 149 (accept_3_2 10 74 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 74 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 74 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 74 149 (Polychromatic418967fa.accept_9_8_2_5_1_237 8
  74 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 74 149 (accept_3_2 7 74 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 74 149 (Polychromatic418967fa.accept_7_6_4_2_1_236 6
  74 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 74 149
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 74 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 74 149 (accept_3_2 4 74 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 74
  149 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 74 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 74 149 (Polychromatic418967fa.accept_13_2_9_6_1_501 2 74 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 149 (accept_3_2 1 74 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 74 149)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73
  149 (allA_of_3_0 73 73 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 72 149 (allA_succ_of_accept 71 72 149
  (Polychromatic418967fa.accept_10_1_2_9_1_152 71 72 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 72 149 (accept_3_2 70 72 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  72 149 (Polychromatic418967fa.accept_13_4_7_6_1_2359 69 72 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 72 149 (Polychromatic418967fa.accept_16_4_8_5_1_3317 68 72 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 72 149 (accept_3_2 67 72 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 72 149 (Polychromatic418967fa.accept_13_1_7_6_1_142 66 72 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 72 149
  (Polychromatic418967fa.accept_17_14_4_13_1_3018 65 72 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 72 149 (accept_3_2 64 72 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  72 149 (Polychromatic418967fa.accept_14_7_2_9_1_2093 63 72 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 72 149 (Polychromatic418967fa.accept_15_2_12_14_1_1709 62 72 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 149 (accept_3_2 61 72 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 72 149 (Polychromatic418967fa.accept_14_4_2_9_1_2092 60 72 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 72 149
  (Polychromatic418967fa.accept_16_11_8_5_1_4366 59 72 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 72 149 (accept_3_2 58 72 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  72 149 (Polychromatic418967fa.accept_10_7_2_9_1_775 57 72 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 72 149 (Polychromatic418967fa.accept_13_4_7_6_1_2359 56 72 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 149 (accept_3_2 55 72 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 72 149 (Polychromatic418967fa.accept_15_9_12_14_1_963 54 72 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 72 149
  (Polychromatic418967fa.accept_13_1_7_6_1_142 53 72 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 72 149 (accept_3_2 52 72 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  72 149 (Polychromatic418967fa.accept_10_1_2_9_1_152 51 72 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 72 149 (Polychromatic418967fa.accept_19_12_15_16_1_6516 50 72 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 72 149 (accept_3_2 49 72 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 72 149 (Polychromatic418967fa.accept_13_9_7_6_1_1673 48 72 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 72 149
  (Polychromatic418967fa.accept_10_7_2_9_1_775 47 72 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 72 149 (accept_3_2 46 72 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  72 149 (Polychromatic418967fa.accept_16_13_8_5_1_3298 45 72 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 72 149 (Polychromatic418967fa.accept_16_12_8_5_1_3316 44 72 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 149 (accept_3_2 43 72 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 72 149 (Polychromatic418967fa.accept_17_8_4_13_1_3014 42 72
  149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 72 149
  (Polychromatic418967fa.accept_10_1_2_9_1_152 41 72 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 72 149 (accept_3_2 40 72 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  72 149 (Polychromatic418967fa.accept_14_11_2_9_1_5873 39 72 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 72 149 (Polychromatic418967fa.accept_13_12_7_6_1_1015 38 72 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 149 (accept_3_2 37 72 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 72 149 (Polychromatic418967fa.accept_16_4_8_5_1_3317 36 72 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 72 149
  (Polychromatic418967fa.accept_13_9_7_6_1_1673 35 72 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 72 149 (accept_3_2 34 72 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  72 149 (Polychromatic418967fa.accept_21_12_9_2_1_7941 33 72 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 72 149 (Polychromatic418967fa.accept_14_4_2_9_1_2092 32 72 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 72 149 (accept_3_2 31 72 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 72 149 (Polychromatic418967fa.accept_13_4_7_6_1_2359 30 72 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 72 149
  (Polychromatic418967fa.accept_16_13_8_5_1_3298 29 72 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 72 149 (accept_3_2 28 72 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  72 149 (Polychromatic418967fa.accept_10_7_2_9_1_775 27 72 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 72 149 (Polychromatic418967fa.accept_15_11_12_14_1_2612 26 72 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 149 (accept_3_2 25 72 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 72 149 (Polychromatic418967fa.accept_15_9_12_14_1_963 24 72
  149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 72 149
  (Polychromatic418967fa.accept_20_3_12_9_1_6410 23 72 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 72 149 (accept_3_2 22 72 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  72 149 (Polychromatic418967fa.accept_10_1_2_9_1_152 21 72 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 72 149 (Polychromatic418967fa.accept_16_4_8_5_1_3317 20 72 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 149 (accept_3_2 19 72 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 72 149 (Polychromatic418967fa.accept_14_4_2_9_1_2092 18 72 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 72 149
  (Polychromatic418967fa.accept_10_7_2_9_1_775 17 72 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 72 149 (accept_3_2 16 72 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  72 149 (Polychromatic418967fa.accept_21_15_9_2_1_7973 15 72 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 72 149 (Polychromatic418967fa.accept_13_1_7_6_1_142 14 72 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 149 (accept_3_2 13 72 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 72 149 (Polychromatic418967fa.accept_13_12_7_6_1_1015 12 72 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 72 149
  (Polychromatic418967fa.accept_10_1_2_9_1_152 11 72 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 72 149 (accept_3_2 10 72 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  72 149 (Polychromatic418967fa.accept_13_9_7_6_1_1673 9 72 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 72 149 (Polychromatic418967fa.accept_17_8_4_13_1_3014 8 72 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 149 (accept_3_2 7 72 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 72 149 (Polychromatic418967fa.accept_19_6_15_16_1_7972 6 72 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 72 149
  (Polychromatic418967fa.accept_25_5_22_24_1_7971 5 72 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 72 149 (accept_3_2 4 72 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 72
  149 (Polychromatic418967fa.accept_16_3_8_5_1_6790 3 72 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 72 149 (Polychromatic418967fa.accept_15_2_12_14_1_1709 2 72 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 149 (accept_3_2 1 72 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 72 149))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 71 149 (allA_succ_of_accept 70 71 149 (accept_3_2 70 71 149 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 71 149 (Polychromatic418967fa.accept_7_6_1_2_1_230 69 71 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 71 149 (Polychromatic418967fa.accept_10_8_1_9_1_413 68 71 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 149 (accept_3_2 67 71 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 66
  71 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 149
  (Polychromatic418967fa.accept_9_2_8_5_1_228 65 71 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 149 (accept_3_2 64 71 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 149 (Polychromatic418967fa.accept_15_3_11_14_1_1705 63 71 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 71 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 149 (accept_3_2 61 71 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 149 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 71 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 149
  (Polychromatic418967fa.accept_7_3_1_2_1_247 59 71 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 149 (accept_3_2 58 71 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 149 (Polychromatic418967fa.accept_9_3_8_5_1_65 57 71 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 149 (Polychromatic418967fa.accept_9_2_8_5_1_228 56 71 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 149 (accept_3_2 55 71 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 71 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 149
  (Polychromatic418967fa.accept_25_3_21_24_1_7970 53 71 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 149 (accept_3_2 52 71 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 149 (Polychromatic418967fa.accept_9_6_8_5_1_837 51 71 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 71 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 149 (accept_3_2 49 71 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 149 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 71 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 149
  (Polychromatic418967fa.accept_9_2_8_5_1_228 47 71 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 149 (accept_3_2 46 71 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 149 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 71 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 149 (Polychromatic418967fa.accept_16_12_7_5_1_1412 44 71 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 149 (accept_3_2 43 71 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 71 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 149
  (Polychromatic418967fa.accept_7_6_1_2_1_230 41 71 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 149 (accept_3_2 40 71 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 149 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 71 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 71 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 149 (accept_3_2 37 71 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 149 (Polychromatic418967fa.accept_14_8_1_9_1_2085 36 71 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 149
  (Polychromatic418967fa.accept_10_5_1_9_1_791 35 71 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 149 (accept_3_2 34 71 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 149 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 71 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 149 (Polychromatic418967fa.accept_10_2_1_9_1_1248 32 71 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 149 (accept_3_2 31 71 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 71 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 149
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 71 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 149 (accept_3_2 28 71 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 149 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 71 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 71 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 149 (accept_3_2 25 71 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 149 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 71 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 149
  (Polychromatic418967fa.accept_11_1_5_6_1_397 23 71 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 149 (accept_3_2 22 71 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 149 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 71 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 149 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 71 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 149 (accept_3_2 19 71 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 71 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 149
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 71 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 149 (accept_3_2 16 71 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 149 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 71 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 71 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 149 (accept_3_2 13 71 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 149 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 71 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 149
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 71 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 149 (accept_3_2 10 71 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 149 (Polychromatic418967fa.accept_19_9_14_16_1_3791 9 71 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 149 (Polychromatic418967fa.accept_10_8_1_9_1_413 8 71 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 149 (accept_3_2 7 71 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 71 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 149
  (Polychromatic418967fa.accept_10_5_1_9_1_791 5 71 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 149 (accept_3_2 4 71 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  149 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 71 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 71 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 149 (accept_3_2 1 71 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 149))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 149
  (allA_of_3_0 70 70 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 69 149 (allA_succ_of_accept 68 69 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 69 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 69 149 (accept_3_2 67 69 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  69 149 (Polychromatic418967fa.accept_7_3_6_2_1_90 66 69 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 69 149 (Polychromatic418967fa.accept_9_2_6_5_1_227 65 69 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 149 (accept_3_2 64 69 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 149 (Polychromatic418967fa.accept_11_8_3_6_1_1855 63 69 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 69 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 69 149 (accept_3_2 61 69 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  69 149 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 69 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 69 149 (Polychromatic418967fa.accept_7_3_6_2_1_90 59 69 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 149 (accept_3_2 58 69 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 149 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 69 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 69 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 149 (accept_3_2 55 69 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  69 149 (Polychromatic418967fa.accept_13_2_4_6_1_2356 54 69 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 69 149 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 69 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 149 (accept_3_2 52 69 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 149 (Polychromatic418967fa.accept_12_3_9_5_1_853 51 69 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 69 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 69 149 (accept_3_2 49 69 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  69 149 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 69 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 69 149 (Polychromatic418967fa.accept_9_2_6_5_1_227 47 69 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 149 (accept_3_2 46 69 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 149 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 69 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 69 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 69 149 (accept_3_2 43 69 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  69 149 (Polychromatic418967fa.accept_11_9_3_6_1_797 42 69 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 69 149 (Polychromatic418967fa.accept_11_8_3_6_1_1855 41 69 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 149 (accept_3_2 40 69 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 149 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 69 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 69 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 149 (accept_3_2 37 69 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  69 149 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 69 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 69 149 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 69 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 149 (accept_3_2 34 69 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 149 (Polychromatic418967fa.accept_13_7_4_6_1_3221 33 69 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 69 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 149 (accept_3_2 31 69 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  69 149 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 69 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 69 149 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 69 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 149 (accept_3_2 28 69 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 149 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 69 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 69 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 69 149 (accept_3_2 25 69 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  69 149 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 69 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 69 149 (Polychromatic418967fa.accept_13_10_4_6_1_3224 23 69 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 149 (accept_3_2 22 69 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 149 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 69 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 69 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 149 (accept_3_2 19 69 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  69 149 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 69 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 69 149 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 69 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 149 (accept_3_2 16 69 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 149 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 69 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 69 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 149 (accept_3_2 13 69 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  69 149 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 69 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 69 149 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 69 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 149 (accept_3_2 10 69 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 149 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 69 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 69 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 149 (accept_3_2 7 69 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69
  149 (Polychromatic418967fa.accept_15_6_9_14_1_3457 6 69 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 69 149 (Polychromatic418967fa.accept_13_5_4_6_1_2371 5 69 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 149 (accept_3_2 4 69 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 149 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 69 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 69 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 69 149 (accept_3_2 1 69 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  149))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 149 (allA_succ_of_accept 67 68
  149 (accept_3_2 67 68 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 68 149
  (Polychromatic418967fa.accept_7_3_5_2_1_17 66 68 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 68 149 (Polychromatic418967fa.accept_8_1_4_5_1_48 65 68 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 68 149 (accept_3_2 64 68 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 68 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 68 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 68 149 (Polychromatic418967fa.accept_12_2_8_5_1_408
  62 68 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 68 149 (accept_3_2 61
  68 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 68 149
  (Polychromatic418967fa.accept_7_4_5_2_1_243 60 68 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 68 149 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 68 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 68 149 (accept_3_2 58 68 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 68 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 68 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 68 149 (Polychromatic418967fa.accept_16_8_4_5_1_4379
  56 68 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 68 149 (accept_3_2 55
  68 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 68 149
  (Polychromatic418967fa.accept_10_4_8_9_1_784 54 68 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 68 149 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 68 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 68 149 (accept_3_2 52 68 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 68 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 68 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 68 149 (Polychromatic418967fa.accept_12_2_8_5_1_408
  50 68 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 68 149 (accept_3_2 49
  68 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 68 149
  (Polychromatic418967fa.accept_11_4_2_6_1_389 48 68 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 68 149 (Polychromatic418967fa.accept_10_7_8_9_1_785 47 68 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 68 149 (accept_3_2 46 68 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 68 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 68 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 68 149 (Polychromatic418967fa.accept_10_4_8_9_1_784
  44 68 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 68 149 (accept_3_2 43
  68 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 68 149
  (Polychromatic418967fa.accept_19_4_11_16_1_1474 42 68 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 68 149 (Polychromatic418967fa.accept_8_1_4_5_1_48 41 68 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 68 149 (accept_3_2 40 68 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 68 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 68 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 68 149 (Polychromatic418967fa.accept_7_3_5_2_1_17 38
  68 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 68 149 (accept_3_2 37 68
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 68 149
  (Polychromatic418967fa.accept_13_10_3_6_1_1003 36 68 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 68 149 (Polychromatic418967fa.accept_13_9_3_6_1_1661 35 68 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 68 149 (accept_3_2 34 68 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 68 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 68 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 149 (Polychromatic418967fa.accept_7_4_5_2_1_243 32
  68 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 68 149 (accept_3_2 31 68
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 68 149
  (Polychromatic418967fa.accept_23_7_22_11_1_6274 30 68 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 68 149 (Polychromatic418967fa.accept_18_11_14_5_1_3951 29 68 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 68 149 (accept_3_2 28 68 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 68 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 68 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 68 149 (Polychromatic418967fa.accept_11_4_2_6_1_389
  26 68 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 68 149 (accept_3_2 25
  68 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 68 149
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 68 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 68 149 (Polychromatic418967fa.accept_13_10_3_6_1_1003 23 68 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 68 149 (accept_3_2 22 68 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 68 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 68 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 68 149 (Polychromatic418967fa.accept_15_5_8_14_1_432
  20 68 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 68 149 (accept_3_2 19
  68 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 68 149
  (Polychromatic418967fa.accept_7_4_5_2_1_243 18 68 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 68 149 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 68 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 68 149 (accept_3_2 16 68 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 68 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 68 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 68 149 (Polychromatic418967fa.accept_10_4_8_9_1_784
  14 68 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 68 149 (accept_3_2 13
  68 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 68 149
  (Polychromatic418967fa.accept_16_12_4_5_1_2273 12 68 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 68 149 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 68 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 68 149 (accept_3_2 10 68 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 68 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 68 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 68 149 (Polychromatic418967fa.accept_16_8_4_5_1_4379 8
  68 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 68 149 (accept_3_2 7 68 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 68 149 (Polychromatic418967fa.accept_15_6_8_14_1_4575
  6 68 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 68 149
  (Polychromatic418967fa.accept_13_5_3_6_1_3278 5 68 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 68 149 (accept_3_2 4 68 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 68
  149 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 68 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 68 149 (Polychromatic418967fa.accept_12_2_8_5_1_408 2 68 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 149 (accept_3_2 1 68 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 68 149)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 149
  (allA_of_3_0 67 67 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 66 149 (allA_succ_of_accept 65 66 149
  (Polychromatic418967fa.accept_9_2_3_5_1_60 65 66 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 66 149 (accept_3_2 64 66 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  66 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 66 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 66 149 (Polychromatic418967fa.accept_7_6_3_2_1_461 62 66 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 66 149 (accept_3_2 61 66 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 66 149 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 66 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 66 149
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 66 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 66 149 (accept_3_2 58 66 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  66 149 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 66 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 66 149 (Polychromatic418967fa.accept_9_2_3_5_1_60 56 66 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 66 149 (accept_3_2 55 66 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 66 149 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 66 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 66 149
  (Polychromatic418967fa.accept_9_8_3_5_1_241 53 66 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 66 149 (accept_3_2 52 66 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  66 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 66 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 66 149 (Polychromatic418967fa.accept_7_1_3_2_1_13 50 66 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 149 (accept_3_2 49 66 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 66 149 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 66 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 66 149
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 66 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 66 149 (accept_3_2 46 66 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  66 149 (Polychromatic418967fa.accept_10_5_6_9_1_2235 45 66 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 66 149 (Polychromatic418967fa.accept_9_8_3_5_1_241 44 66 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 66 149 (accept_3_2 43 66 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 66 149 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 66 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 66 149
  (Polychromatic418967fa.accept_7_6_3_2_1_461 41 66 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 66 149 (accept_3_2 40 66 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  66 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 66 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 66 149 (Polychromatic418967fa.accept_9_2_3_5_1_60 38 66 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 66 149 (accept_3_2 37 66 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 66 149 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 66 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 66 149
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 66 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 66 149 (accept_3_2 34 66 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  66 149 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 66 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 66 149 (Polychromatic418967fa.accept_23_9_20_11_1_4501 32 66 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 149 (accept_3_2 31 66 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 66 149 (Polychromatic418967fa.accept_20_10_6_9_1_4989 30 66
  149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 66 149
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 66 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 66 149 (accept_3_2 28 66 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  66 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 66 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 66 149 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 66 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 149 (accept_3_2 25 66 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 66 149 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 66 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 66 149
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 66 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 66 149 (accept_3_2 22 66 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  66 149 (Polychromatic418967fa.accept_13_8_1_6_1_997 21 66 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 66 149 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 66 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 149 (accept_3_2 19 66 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 66 149 (Polychromatic418967fa.accept_13_5_1_6_1_2367 18 66 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 66 149
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 66 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 66 149 (accept_3_2 16 66 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  66 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 66 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 66 149 (Polychromatic418967fa.accept_19_14_9_16_1_7969 14 66 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 149 (accept_3_2 13 66 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 66 149 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 66 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 66 149
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 66 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 66 149 (accept_3_2 10 66 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  66 149 (Polychromatic418967fa.accept_13_9_1_6_1_510 9 66 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 66 149 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 66 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 149 (accept_3_2 7 66 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 66 149 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 66 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 66 149
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 66 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 66 149 (accept_3_2 4 66 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 66
  149 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 66 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 66 149 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 66 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 149 (accept_3_2 1 66 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 66 149)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 149
  (allA_succ_of_accept 64 65 149 (accept_3_2 64 65 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  65 149 (Polychromatic418967fa.accept_16_15_1_5_1_2265 63 65 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 65 149 (Polychromatic418967fa.accept_9_8_2_5_1_237 62 65 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 149 (accept_3_2 61 65 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 65 149 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 65 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 149
  (Polychromatic418967fa.accept_24_11_17_5_1_7968 59 65 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 65 149 (accept_3_2 58 65 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  65 149 (Polychromatic418967fa.accept_9_3_2_5_1_234 57 65 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 65 149 (Polychromatic418967fa.accept_10_6_5_9_1_1233 56 65 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 149 (accept_3_2 55 65 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 65 149 (Polychromatic418967fa.accept_10_4_5_9_1_1231 54 65 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 149
  (Polychromatic418967fa.accept_9_8_2_5_1_237 53 65 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 65 149 (accept_3_2 52 65 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  65 149 (Polychromatic418967fa.accept_9_6_2_5_1_506 51 65 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 65 149 (Polychromatic418967fa.accept_18_14_11_5_1_7967 50 65 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 149 (accept_3_2 49 65 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 149 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 65 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 149
  (Polychromatic418967fa.accept_15_2_5_14_1_61 47 65 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 65 149 (accept_3_2 46 65 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  65 149 (Polychromatic418967fa.accept_16_13_1_5_1_5469 45 65 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 65 149 (Polychromatic418967fa.accept_8_4_1_5_1_186 44 65 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 149 (accept_3_2 43 65 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 149 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 65 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 149
  (Polychromatic418967fa.accept_10_1_5_9_1_157 41 65 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 65 149 (accept_3_2 40 65 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  65 149 (Polychromatic418967fa.accept_9_3_2_5_1_234 39 65 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 65 149 (Polychromatic418967fa.accept_11_5_10_6_1_793 38 65 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 149 (accept_3_2 37 65 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 149 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 65 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 149
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 65 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 65 149 (accept_3_2 34 65 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  65 149 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 65 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 149 (Polychromatic418967fa.accept_15_2_5_14_1_61 32 65 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 149 (accept_3_2 31 65 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 65 149 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 65 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 149
  (Polychromatic418967fa.accept_16_13_1_5_1_5469 29 65 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 149 (accept_3_2 28 65 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  65 149 (Polychromatic418967fa.accept_11_5_10_6_1_793 27 65 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 65 149 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 65 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 149 (accept_3_2 25 65 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 149 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 65 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 149
  (Polychromatic418967fa.accept_15_8_5_14_1_986 23 65 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 149 (accept_3_2 22 65 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 149 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 65 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 149 (Polychromatic418967fa.accept_8_4_1_5_1_186 20 65 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 149 (accept_3_2 19 65 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 149 (Polychromatic418967fa.accept_17_1_14_13_1_7966 18 65 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 149
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 65 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 149 (accept_3_2 16 65 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 149 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 65 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 149 (Polychromatic418967fa.accept_10_4_5_9_1_1231 14 65 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 149 (accept_3_2 13 65 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 149 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 65 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 149
  (Polychromatic418967fa.accept_10_1_5_9_1_157 11 65 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 149 (accept_3_2 10 65 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 149 (Polychromatic418967fa.accept_15_9_5_14_1_973 9 65 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 149 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 65 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 149 (accept_3_2 7 65 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 149 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 65 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 149
  (Polychromatic418967fa.accept_11_5_10_6_1_793 5 65 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 149 (accept_3_2 4 65 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  149 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 65 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 149 (Polychromatic418967fa.accept_15_2_5_14_1_61 2 65 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 149 (accept_3_2 1 65 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 149))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 149
  (allA_of_3_0 64 64 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 63 149 (allA_succ_of_accept 62 63 149
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 63 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 149 (accept_3_2 61 63 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  63 149 (Polychromatic418967fa.accept_13_8_11_6_1_1035 60 63 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 63 149 (Polychromatic418967fa.accept_20_19_3_9_1_7965 59 63 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 149 (accept_3_2 58 63 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 149 (Polychromatic418967fa.accept_12_9_3_5_1_423 57 63 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 63 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 63 149 (accept_3_2 55 63 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  63 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 63 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 63 149 (Polychromatic418967fa.accept_19_15_6_16_1_6506 53 63 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 149 (accept_3_2 52 63 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 149 (Polychromatic418967fa.accept_18_15_9_5_1_3934 51 63
  149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 149
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 63 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 149 (accept_3_2 49 63 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  63 149 (Polychromatic418967fa.accept_18_12_9_5_1_2771 48 63 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 63 149 (Polychromatic418967fa.accept_11_3_8_6_1_788 47 63 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 149 (accept_3_2 46 63 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 149 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 63 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 63 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 149 (accept_3_2 43 63 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  63 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 63 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 63 149 (Polychromatic418967fa.accept_15_11_3_14_1_971 41 63 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 149 (accept_3_2 40 63 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 149 (Polychromatic418967fa.accept_20_19_3_9_1_7965 39 63
  149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 149
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 63 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 149 (accept_3_2 37 63 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  63 149 (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 63 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 63 149 (Polychromatic418967fa.accept_17_1_12_13_1_448 35 63 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 149 (accept_3_2 34 63 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 149 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 63 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 63 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 149 (accept_3_2 31 63 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  63 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 63 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 63 149 (Polychromatic418967fa.accept_19_10_6_16_1_7964 29 63 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 149 (accept_3_2 28 63 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 149 (Polychromatic418967fa.accept_19_8_6_16_1_6505 27 63
  149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 149
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 63 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 149 (accept_3_2 25 63 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  63 149 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 63 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 63 149 (Polychromatic418967fa.accept_24_23_15_5_1_7963 23 63 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 149 (accept_3_2 22 63 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 149 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 63 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 63 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 149 (accept_3_2 19 63 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  63 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 63 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 63 149 (Polychromatic418967fa.accept_13_4_11_6_1_1033 17 63 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 149 (accept_3_2 16 63 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 149 (Polychromatic418967fa.accept_18_15_9_5_1_3934 15 63
  149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 149
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 63 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 149 (accept_3_2 13 63 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  63 149 (Polychromatic418967fa.accept_14_12_7_9_1_726 12 63 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 63 149 (Polychromatic418967fa.accept_15_11_3_14_1_971 11 63 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 149 (accept_3_2 10 63 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 149 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 63 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 63 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 149 (accept_3_2 7 63 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63
  149 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 63 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 149 (Polychromatic418967fa.accept_13_5_11_6_1_505 5 63 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 149 (accept_3_2 4 63 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 63 149 (Polychromatic418967fa.accept_11_3_8_6_1_788 3 63 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 63
  149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 149 (accept_3_2 1 63 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  149))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 149 (allA_succ_of_accept 61 62 149
  (accept_3_2 61 62 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 62 149
  (Polychromatic418967fa.accept_7_4_6_2_1_451 60 62 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 62 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 62 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 62 149 (accept_3_2 58 62 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 62 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 62 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 62 149 (Polychromatic418967fa.accept_9_2_8_5_1_228 56
  62 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 62 149 (accept_3_2 55 62
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 62 149
  (Polychromatic418967fa.accept_13_2_10_6_1_1676 54 62 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 62 149 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 62 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 62 149 (accept_3_2 52 62 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 62 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 62 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 62 149 (Polychromatic418967fa.accept_7_1_6_2_1_18 50
  62 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 62 149 (accept_3_2 49 62
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 62 149 (Polychromatic418967fa.accept_9_3_8_5_1_65
  48 62 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 62 149
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 62 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 62 149 (accept_3_2 46 62 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  62 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 62 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 62 149 (Polychromatic418967fa.accept_12_8_2_5_1_844 44 62 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 62 149 (accept_3_2 43 62 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 62 149 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 62 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 62 149
  (Polychromatic418967fa.accept_10_1_2_9_1_152 41 62 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 62 149 (accept_3_2 40 62 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  62 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 62 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 62 149 (Polychromatic418967fa.accept_7_3_6_2_1_90 38 62 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 62 149 (accept_3_2 37 62 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 62 149 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 62 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 62 149
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 62 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 62 149 (accept_3_2 34 62 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  62 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 62 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 62 149 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 62 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 62 149 (accept_3_2 31 62 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 62 149 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 62 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 62 149
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 62 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 62 149 (accept_3_2 28 62 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  62 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 62 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 62 149 (Polychromatic418967fa.accept_16_10_14_5_1_5496 26 62 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 62 149 (accept_3_2 25 62 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 62 149 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 62 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 62 149
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 62 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 62 149 (accept_3_2 22 62 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  62 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 62 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 62 149 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 62 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 62 149 (accept_3_2 19 62 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 62 149 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 62 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 62 149
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 62 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 62 149 (accept_3_2 16 62 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  62 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 62 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 62 149 (Polychromatic418967fa.accept_18_14_8_5_1_860 14 62 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 62 149 (accept_3_2 13 62 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 62 149 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 62 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 62 149
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 62 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 62 149 (accept_3_2 10 62 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  62 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 62 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 62 149 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 62 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 62 149 (accept_3_2 7 62 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 62 149 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 62 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 62 149
  (Polychromatic418967fa.accept_13_5_10_6_1_2361 5 62 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 62 149 (accept_3_2 4 62 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 62
  149 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 62 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 62 149 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 62 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 149 (accept_3_2 1 62 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 62 149)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 149
  (allA_of_3_0 61 61 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 60 149 (allA_succ_of_accept 59 60 149
  (Polychromatic418967fa.accept_19_2_3_16_1_6469 59 60 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 60 149 (accept_3_2 58 60 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  60 149 (Polychromatic418967fa.accept_8_1_4_5_1_48 57 60 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 60 149 (Polychromatic418967fa.accept_9_2_6_5_1_227 56 60 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 60 149 (accept_3_2 55 60 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 60 149 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 60 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 60 149
  (Polychromatic418967fa.accept_9_8_6_5_1_513 53 60 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 60 149 (accept_3_2 52 60 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  60 149 (Polychromatic418967fa.accept_18_15_6_5_1_3972 51 60 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 60 149 (Polychromatic418967fa.accept_13_11_8_6_1_1023 50 60 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 60 149 (accept_3_2 49 60 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 60 149 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 60 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 60 149
  (Polychromatic418967fa.accept_7_5_4_2_1_235 47 60 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 60 149 (accept_3_2 46 60 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  60 149 (Polychromatic418967fa.accept_11_1_5_6_1_397 45 60 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 60 149 (Polychromatic418967fa.accept_9_8_6_5_1_513 44 60 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 149 (accept_3_2 43 60 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 60 149 (Polychromatic418967fa.accept_16_10_12_5_1_2254 42 60 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 60 149
  (Polychromatic418967fa.accept_7_6_4_2_1_236 41 60 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 60 149 (accept_3_2 40 60 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  60 149 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 60 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 60 149 (Polychromatic418967fa.accept_9_2_6_5_1_227 38 60 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 149 (accept_3_2 37 60 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 60 149 (Polychromatic418967fa.accept_16_4_12_5_1_2287 36 60 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 60 149
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 60 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 60 149 (accept_3_2 34 60 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  60 149 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 60 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 60 149 (Polychromatic418967fa.accept_11_10_5_6_1_1842 32 60 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 149 (accept_3_2 31 60 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 60 149 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 60 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 60 149
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 60 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 60 149 (accept_3_2 28 60 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  60 149 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 60 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 60 149 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 60 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 60 149 (accept_3_2 25 60 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 60 149 (Polychromatic418967fa.accept_13_11_8_6_1_1023 24 60 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 60 149
  (Polychromatic418967fa.accept_11_1_5_6_1_397 23 60 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 60 149 (accept_3_2 22 60 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  60 149 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 60 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 60 149 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 60 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 149 (accept_3_2 19 60 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 60 149 (Polychromatic418967fa.accept_19_18_3_16_1_7962 18 60 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 60 149
  (Polychromatic418967fa.accept_8_1_4_5_1_48 17 60 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 60 149 (accept_3_2 16 60 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  60 149 (Polychromatic418967fa.accept_13_2_8_6_1_2390 15 60 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 60 149 (Polychromatic418967fa.accept_13_1_8_6_1_1016 14 60 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 149 (accept_3_2 13 60 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 60 149 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 60 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 60 149
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 60 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 60 149 (accept_3_2 10 60 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  60 149 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 60 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 60 149 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 60 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 149 (accept_3_2 7 60 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 60 149 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 60 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 60 149
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 60 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 60 149 (accept_3_2 4 60 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 60
  149 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 60 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 60 149 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 60 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 149 (accept_3_2 1 60 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 60 149)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 149
  (allA_succ_of_accept 58 59 149 (accept_3_2 58 59 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  59 149 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 59 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 59 149 (Polychromatic418967fa.accept_13_4_7_6_1_2359 56 59 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 149 (accept_3_2 55 59 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 59 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 59 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 149
  (Polychromatic418967fa.accept_13_1_7_6_1_142 53 59 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 149 (accept_3_2 52 59 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 149 (Polychromatic418967fa.accept_13_12_7_6_1_1015 51 59 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 59 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 149 (accept_3_2 49 59 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 149 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 59 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 149
  (Polychromatic418967fa.accept_7_5_3_2_1_249 47 59 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 149 (accept_3_2 46 59 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 149 (Polychromatic418967fa.accept_19_7_2_16_1_1496 45 59 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 149 (Polychromatic418967fa.accept_20_4_19_9_1_7961 44 59 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 149 (accept_3_2 43 59 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 59 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 149
  (Polychromatic418967fa.accept_7_6_3_2_1_461 41 59 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 149 (accept_3_2 40 59 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 149 (Polychromatic418967fa.accept_16_7_11_5_1_4402 39 59 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 59 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 149 (accept_3_2 37 59 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 149 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 59 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 149
  (Polychromatic418967fa.accept_11_2_4_6_1_2412 35 59 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 149 (accept_3_2 34 59 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 149 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 59 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 149 (Polychromatic418967fa.accept_17_15_8_13_1_6628 32 59 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 149 (accept_3_2 31 59 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 59 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 149
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 59 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 149 (accept_3_2 28 59 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 149 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 59 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 59 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 149 (accept_3_2 25 59 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 149 (Polychromatic418967fa.accept_11_2_4_6_1_2412 24 59 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 149
  (Polychromatic418967fa.accept_16_7_11_5_1_4402 23 59 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 149 (accept_3_2 22 59 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 149 (Polychromatic418967fa.accept_17_4_8_13_1_7960 21 59 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 149 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 59 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 149 (accept_3_2 19 59 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 59 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 149
  (Polychromatic418967fa.accept_13_4_7_6_1_2359 17 59 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 149 (accept_3_2 16 59 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 149 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 59 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 59 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 149 (accept_3_2 13 59 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 149 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 59 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 149
  (Polychromatic418967fa.accept_19_11_2_16_1_3822 11 59 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 149 (accept_3_2 10 59 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 149 (Polychromatic418967fa.accept_13_9_7_6_1_1673 9 59 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 149 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 59 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 149 (accept_3_2 7 59 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 59 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 149
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 59 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 149 (accept_3_2 4 59 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  149 (Polychromatic418967fa.accept_17_3_8_13_1_5361 3 59 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 59 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 59 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 149 (accept_3_2 1 59 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 59 149))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 149
  (allA_of_3_0 58 58 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 57 149 (allA_succ_of_accept 56 57 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 57 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 149 (accept_3_2 55 57 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  57 149 (Polychromatic418967fa.accept_15_9_12_14_1_963 54 57 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 57 149 (Polychromatic418967fa.accept_9_8_3_5_1_241 53 57 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 149 (accept_3_2 52 57 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 149 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 57 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 57 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 149 (accept_3_2 49 57 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  57 149 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 57 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 57 149 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 57 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 149 (accept_3_2 46 57 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 149 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 57 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 57 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 149 (accept_3_2 43 57 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  57 149 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 57 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 57 149 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 57 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 149 (accept_3_2 40 57 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 149 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 57 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 57 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 149 (accept_3_2 37 57 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  57 149 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 57 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 57 149 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 57 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 149 (accept_3_2 34 57 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 149 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 57 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 57 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 149 (accept_3_2 31 57 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  57 149 (Polychromatic418967fa.accept_13_4_5_6_1_3201 30 57 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 57 149 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 57 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 149 (accept_3_2 28 57 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 149 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 57 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 57 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 149 (accept_3_2 25 57 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  57 149 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 57 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 57 149 (Polychromatic418967fa.accept_13_10_5_6_1_1671 23 57 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 149 (accept_3_2 22 57 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 149 (Polychromatic418967fa.accept_22_21_13_17_1_7959 21 57
  149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 57 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 149 (accept_3_2 19 57 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  57 149 (Polychromatic418967fa.accept_10_8_7_9_1_425 18 57 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 57 149 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 57 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 149 (accept_3_2 16 57 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 149 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 57 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 57 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 149 (accept_3_2 13 57 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  57 149 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 57 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 57 149 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 57 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 149 (accept_3_2 10 57 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 149 (Polychromatic418967fa.accept_15_9_12_14_1_963 9 57 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 57 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 149 (accept_3_2 7 57 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57
  149 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 57 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 149 (Polychromatic418967fa.accept_25_5_7_24_1_7958 5 57 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 149 (accept_3_2 4 57 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 149 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 57 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 57
  149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 149 (accept_3_2 1 57 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 149)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 149 (allA_succ_of_accept 55 56 149 (accept_3_2 55 56 149 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 56 149 (Polychromatic418967fa.accept_13_2_4_6_1_2356 54 56 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 56 149 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 56 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 149 (accept_3_2 52 56 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 56 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 51
  56 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 56 149
  (Polychromatic418967fa.accept_12_2_8_5_1_408 50 56 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 56 149 (accept_3_2 49 56 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  56 149 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 56 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 56 149 (Polychromatic418967fa.accept_19_9_18_16_1_7938 47 56 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 149 (accept_3_2 46 56 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 56 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 56 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 149
  (Polychromatic418967fa.accept_9_8_2_5_1_237 44 56 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 56 149 (accept_3_2 43 56 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  56 149 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 56 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 56 149 (Polychromatic418967fa.accept_13_2_4_6_1_2356 41 56 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 56 149 (accept_3_2 40 56 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 56 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 56 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 149
  (Polychromatic418967fa.accept_11_5_1_6_1_774 38 56 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 56 149 (accept_3_2 37 56 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  56 149 (Polychromatic418967fa.accept_13_10_4_6_1_3224 36 56 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 56 149 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 56 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 56 149 (accept_3_2 34 56 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 56 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 56 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 56 149
  (Polychromatic418967fa.accept_17_15_5_13_1_6626 32 56 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 56 149 (accept_3_2 31 56 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  56 149 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 56 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 56 149 (Polychromatic418967fa.accept_11_7_1_6_1_1281 29 56 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 56 149 (accept_3_2 28 56 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 56 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 56 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 149
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 56 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 56 149 (accept_3_2 25 56 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  56 149 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 56 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 56 149 (Polychromatic418967fa.accept_10_3_6_9_1_779 23 56 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 149 (accept_3_2 22 56 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 56 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 56 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 56 149
  (Polychromatic418967fa.accept_13_7_4_6_1_3221 20 56 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 56 149 (accept_3_2 19 56 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  56 149 (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 56 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 56 149 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 56 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 149 (accept_3_2 16 56 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 56 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 56 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 56 149
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 56 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 56 149 (accept_3_2 13 56 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  56 149 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 56 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 56 149 (Polychromatic418967fa.accept_13_11_4_6_1_1006 11 56 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 149 (accept_3_2 10 56 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 56 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 56 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 149
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 56 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 56 149 (accept_3_2 7 56 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 56
  149 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 56 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 56 149 (Polychromatic418967fa.accept_10_5_6_9_1_2235 5 56 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 149 (accept_3_2 4 56 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 56 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 56 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 149 (Polychromatic418967fa.accept_12_2_8_5_1_408 2
  56 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 56 149 (accept_3_2 1 56 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 149))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 55 149 (allA_of_3_0 55 55 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 54 149
  (allA_succ_of_accept 53 54 149 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 54 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 54 149 (accept_3_2 52 54 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 54 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 54 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 54 149 (Polychromatic418967fa.accept_15_5_9_14_1_1724
  50 54 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 149 (accept_3_2 49
  54 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 149
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 48 54 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 54 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 54 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 54 149 (accept_3_2 46 54 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 54 149 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 54 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 54 149
  (Polychromatic418967fa.accept_17_10_3_13_1_6639 44 54 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 54 149 (accept_3_2 43 54 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  54 149 (Polychromatic418967fa.accept_15_12_9_14_1_2635 42 54 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 54 149 (Polychromatic418967fa.accept_34_7_20_13_1_7957 41 54 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 54 149 (accept_3_2 40 54 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 54 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 54 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 54 149
  (Polychromatic418967fa.accept_7_3_5_2_1_17 38 54 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 54 149 (accept_3_2 37 54 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  54 149 (Polychromatic418967fa.accept_13_10_2_6_1_1044 36 54 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 54 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 54 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 54 149 (accept_3_2 34 54 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 54 149 (Polychromatic418967fa.accept_10_3_4_9_1_15 33 54 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 54 149
  (Polychromatic418967fa.accept_7_4_5_2_1_243 32 54 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 54 149 (accept_3_2 31 54 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  54 149 (Polychromatic418967fa.accept_13_4_2_6_1_1043 30 54 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 54 149 (Polychromatic418967fa.accept_22_7_10_17_1_7956 29 54 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 54 149 (accept_3_2 28 54 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 54 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 54 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 149
  (Polychromatic418967fa.accept_20_6_14_9_1_3489 26 54 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 54 149 (accept_3_2 25 54 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  54 149 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 54 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 54 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 54 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 54 149 (accept_3_2 22 54 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 54 149 (Polychromatic418967fa.accept_13_8_2_6_1_2385 21 54 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 149
  (Polychromatic418967fa.accept_15_5_9_14_1_1724 20 54 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 54 149 (accept_3_2 19 54 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  54 149 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 54 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 54 149 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 54 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 54 149 (accept_3_2 16 54 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 54 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 54 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 149
  (Polychromatic418967fa.accept_13_1_2_6_1_515 14 54 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 54 149 (accept_3_2 13 54 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  54 149 (Polychromatic418967fa.accept_13_12_2_6_1_2396 12 54 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 54 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 54 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 54 149 (accept_3_2 10 54 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 54 149 (Polychromatic418967fa.accept_13_9_2_6_1_514 9 54 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 149
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 54 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 54 149 (accept_3_2 7 54 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54
  149 (Polychromatic418967fa.accept_15_6_9_14_1_3457 6 54 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 54 149 (Polychromatic418967fa.accept_10_5_4_9_1_420 5 54 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 149 (accept_3_2 4 54 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 54 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 54 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 149
  (Polychromatic418967fa.accept_25_2_4_24_1_7955 2 54 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 54 149 (accept_3_2 1 54 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  149)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 149 (allA_succ_of_accept 52 53 149 (accept_3_2
  52 53 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 149
  (Polychromatic418967fa.accept_9_6_8_5_1_837 51 53 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 149 (Polychromatic418967fa.accept_15_5_8_14_1_432 50 53 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 149 (accept_3_2 49 53 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 149 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 53 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 149 (Polychromatic418967fa.accept_7_5_4_2_1_235 47
  53 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 149 (accept_3_2 46 53
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 149
  (Polychromatic418967fa.accept_23_22_7_11_1_7954 45 53 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 53 149 (Polychromatic418967fa.accept_10_4_3_9_1_1262 44 53 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 149 (accept_3_2 43 53 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 53 149 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 53 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 149 (Polychromatic418967fa.accept_7_6_4_2_1_236 41
  53 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 53 149 (accept_3_2 40 53
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 53 149 (Polychromatic418967fa.accept_9_3_8_5_1_65
  39 53 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 53 149
  (Polychromatic418967fa.accept_9_2_8_5_1_228 38 53 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 53 149 (accept_3_2 37 53 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  53 149 (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 53 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 53 149 (Polychromatic418967fa.accept_13_9_1_6_1_510 35 53 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 53 149 (accept_3_2 34 53 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 53 149 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 53 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 53 149
  (Polychromatic418967fa.accept_17_15_2_13_1_4153 32 53 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 53 149 (accept_3_2 31 53 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  53 149 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 53 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 53 149 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 53 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 53 149 (accept_3_2 28 53 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 53 149 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 53 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 53 149
  (Polychromatic418967fa.accept_7_5_4_2_1_235 26 53 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 53 149 (accept_3_2 25 53 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  53 149 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 53 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 53 149 (Polychromatic418967fa.accept_17_6_2_13_1_3051 23 53 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 53 149 (accept_3_2 22 53 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 53 149 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 53 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 53 149
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 53 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 53 149 (accept_3_2 19 53 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  53 149 (Polychromatic418967fa.accept_13_5_1_6_1_2367 18 53 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 53 149 (Polychromatic418967fa.accept_21_17_11_2_1_7953 17 53 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 53 149 (accept_3_2 16 53 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 53 149 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 53 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 53 149
  (Polychromatic418967fa.accept_10_4_3_9_1_1262 14 53 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 53 149 (accept_3_2 13 53 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  53 149 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 53 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 53 149 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 53 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 53 149 (accept_3_2 10 53 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 53 149 (Polychromatic418967fa.accept_13_9_1_6_1_510 9 53 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 53 149
  (Polychromatic418967fa.accept_13_8_1_6_1_997 8 53 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 53 149 (accept_3_2 7 53 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 53
  149 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 53 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 53 149 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 53 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 53 149 (accept_3_2 4 53 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 53 149 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 53 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 53 149 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  53 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 149 (accept_3_2 1 53 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 53 149)))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 52 149 (allA_of_3_0 52 52 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 149
  (allA_succ_of_accept 50 51 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 51 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 149 (accept_3_2 49 51 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 51 149 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 51 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 149 (Polychromatic418967fa.accept_9_2_6_5_1_227 47
  51 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 149 (accept_3_2 46 51
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 149
  (Polychromatic418967fa.accept_10_5_1_9_1_791 45 51 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 51 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 51 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 149 (accept_3_2 43 51 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 51 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 51 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 149 (Polychromatic418967fa.accept_13_2_12_6_1_2394
  41 51 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 149 (accept_3_2 40
  51 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 149
  (Polychromatic418967fa.accept_9_3_6_5_1_63 39 51 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 51 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 51 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 149 (accept_3_2 37 51 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 51 149 (Polychromatic418967fa.accept_13_10_12_6_1_991 36 51 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 51 149
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 51 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 51 149 (accept_3_2 34 51 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  51 149 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 51 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 51 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 51 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 149 (accept_3_2 31 51 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 51 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 51 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 149
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 51 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 51 149 (accept_3_2 28 51 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  51 149 (Polychromatic418967fa.accept_18_9_15_5_1_6551 27 51 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 51 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 51 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 149 (accept_3_2 25 51 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 51 149 (Polychromatic418967fa.accept_15_9_6_14_1_2627 24 51 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 51 149
  (Polychromatic418967fa.accept_11_1_7_6_1_378 23 51 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 51 149 (accept_3_2 22 51 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  51 149 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 51 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 51 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 51 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 149 (accept_3_2 19 51 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 51 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 51 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 51 149
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 51 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 51 149 (accept_3_2 16 51 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  51 149 (Polychromatic418967fa.accept_10_5_1_9_1_791 15 51 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 51 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 51 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 149 (accept_3_2 13 51 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 51 149 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 51 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 149
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 51 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 51 149 (accept_3_2 10 51 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  51 149 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 51 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 51 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 51 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 149 (accept_3_2 7 51 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 51 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 51 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 51 149
  (Polychromatic418967fa.accept_10_5_1_9_1_791 5 51 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 51 149 (accept_3_2 4 51 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 51
  149 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 51 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 51 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 51 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 149 (accept_3_2 1 51 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 51 149))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 149 (allA_succ_of_accept
  49 50 149 (accept_3_2 49 50 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 50 149
  (Polychromatic418967fa.accept_7_6_1_2_1_230 48 50 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 50 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 50 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 149 (accept_3_2 46 50 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 50 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 50 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 50 149 (Polychromatic418967fa.accept_12_8_2_5_1_844
  44 50 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 50 149 (accept_3_2 43
  50 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 50 149
  (Polychromatic418967fa.accept_19_4_12_16_1_2574 42 50 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 50 149 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 50 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 50 149 (accept_3_2 40 50 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 50 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 50 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 149 (Polychromatic418967fa.accept_7_3_1_2_1_247 38
  50 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 50 149 (accept_3_2 37 50
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 50 149
  (Polychromatic418967fa.accept_15_6_5_14_1_429 36 50 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 50 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 50 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 50 149 (accept_3_2 34 50 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 50 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 50 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 50 149 (Polychromatic418967fa.accept_12_8_2_5_1_844
  32 50 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 50 149 (accept_3_2 31
  50 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 50 149
  (Polychromatic418967fa.accept_13_4_11_6_1_1033 30 50 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 50 149 (Polychromatic418967fa.accept_14_1_8_9_1_1312 29 50 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 149 (accept_3_2 28 50 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 50 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 50 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 149
  (Polychromatic418967fa.accept_17_9_16_13_1_6636 26 50 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 50 149 (accept_3_2 25 50 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  50 149 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 50 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 50 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 50 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 149 (accept_3_2 22 50 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 50 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 50 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 50 149
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 50 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 50 149 (accept_3_2 19 50 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  50 149 (Polychromatic418967fa.accept_13_5_11_6_1_505 18 50 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 50 149 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 50 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 149 (accept_3_2 16 50 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 50 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 50 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 50 149
  (Polychromatic418967fa.accept_19_14_12_16_1_7952 14 50 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 50 149 (accept_3_2 13 50 149 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 50 149 (Polychromatic418967fa.accept_17_12_16_13_1_7951 12 50 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 50 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 50 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 50 149 (accept_3_2 10 50 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 50 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 50
  149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 149
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 50 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 50 149 (accept_3_2 7 50 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50
  149 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 50 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 50 149 (Polychromatic418967fa.accept_13_5_11_6_1_505 5 50 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 50 149 (accept_3_2 4 50 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 50 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 50 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 149 (Polychromatic418967fa.accept_15_2_5_14_1_61 2
  50 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 50 149 (accept_3_2 1 50 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 149)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  49 149 (allA_of_3_0 49 49 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 48 149 (allA_succ_of_accept 47 48
  149 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 48 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 48 149 (accept_3_2 46 48 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  48 149 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 48 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 48 149 (Polychromatic418967fa.accept_9_8_3_5_1_241 44 48 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 149 (accept_3_2 43 48 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 48 149 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 48 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 48 149
  (Polychromatic418967fa.accept_10_1_8_9_1_787 41 48 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 48 149 (accept_3_2 40 48 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  48 149 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 48 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 48 149 (Polychromatic418967fa.accept_7_3_6_2_1_90 38 48 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 149 (accept_3_2 37 48 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 149 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 48 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 48 149
  (Polychromatic418967fa.accept_9_8_3_5_1_241 35 48 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 48 149 (accept_3_2 34 48 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  48 149 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 48 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 48 149 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 48 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 149 (accept_3_2 31 48 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 149 (Polychromatic418967fa.accept_13_4_9_6_1_2376 30 48 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 48 149
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 48 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 48 149 (accept_3_2 28 48 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  48 149 (Polychromatic418967fa.accept_10_7_8_9_1_785 27 48 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 48 149 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 48 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 149 (accept_3_2 25 48 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 149 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 48 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 48 149
  (Polychromatic418967fa.accept_13_10_9_6_1_1026 23 48 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 48 149 (accept_3_2 22 48 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  48 149 (Polychromatic418967fa.accept_10_1_8_9_1_787 21 48 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 48 149 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 48 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 149 (accept_3_2 19 48 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 48 149 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 48 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 48 149
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 48 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 48 149 (accept_3_2 16 48 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  48 149 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 48 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 48 149 (Polychromatic418967fa.accept_10_4_8_9_1_784 14 48 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 149 (accept_3_2 13 48 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 48 149 (Polychromatic418967fa.accept_21_12_6_2_1_7950 12 48 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 48 149
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 48 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 48 149 (accept_3_2 10 48 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  48 149 (Polychromatic418967fa.accept_18_9_12_5_1_864 9 48 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 48 149 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 48 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 149 (accept_3_2 7 48 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 149 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 48 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 48 149
  (Polychromatic418967fa.accept_19_5_10_16_1_6507 5 48 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 48 149 (accept_3_2 4 48 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 48
  149 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 48 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 48 149 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 48 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 149 (accept_3_2 1 48 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 48 149)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 149 (allA_succ_of_accept 46
  47 149 (accept_3_2 46 47 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 149
  (Polychromatic418967fa.accept_7_3_5_2_1_17 45 47 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 149 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 47 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 149 (accept_3_2 43 47 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 47 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 149 (Polychromatic418967fa.accept_11_8_3_6_1_1855
  41 47 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 149 (accept_3_2 40
  47 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 149
  (Polychromatic418967fa.accept_7_4_5_2_1_243 39 47 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 47 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 47 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 149 (accept_3_2 37 47 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 47 149 (Polychromatic418967fa.accept_16_4_15_5_1_5537 36 47 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 149
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 47 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 149 (accept_3_2 34 47 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 149 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 47 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 149 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 47 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 149 (accept_3_2 31 47 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 47 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 149
  (Polychromatic418967fa.accept_19_10_9_16_1_5085 29 47 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 149 (accept_3_2 28 47 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 149 (Polychromatic418967fa.accept_13_1_8_6_1_1016 27 47 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 47 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 149 (accept_3_2 25 47 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 149 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 47 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 149
  (Polychromatic418967fa.accept_19_4_9_16_1_3811 23 47 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 149 (accept_3_2 22 47 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 149 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 47 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 149 (Polychromatic418967fa.accept_11_9_3_6_1_797 20 47 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 149 (accept_3_2 19 47 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 47 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 149
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 47 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 149 (accept_3_2 16 47 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 149 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 47 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 47 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 149 (accept_3_2 13 47 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 149 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 47 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 149
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 47 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 149 (accept_3_2 10 47 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 149 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 47 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 149 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 47 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 149 (accept_3_2 7 47 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 47 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 149
  (Polychromatic418967fa.accept_15_5_2_14_1_1693 5 47 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 149 (accept_3_2 4 47 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  149 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 47 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 47 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 149 (accept_3_2 1 47 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 149))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 149 (allA_of_3_0 46 46 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 45 149 (allA_succ_of_accept 44 45 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 45 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 149 (accept_3_2 43 45 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  45 149 (Polychromatic418967fa.accept_16_10_13_5_1_3292 42 45 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 45 149 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 45 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 149 (accept_3_2 40 45 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 149 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 45 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 45 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 149 (accept_3_2 37 45 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  45 149 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 45 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 45 149 (Polychromatic418967fa.accept_20_15_5_9_1_3479 35 45 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 149 (accept_3_2 34 45 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 149 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 45 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 45 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 149 (accept_3_2 31 45 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  45 149 (Polychromatic418967fa.accept_18_12_9_5_1_2771 30 45 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 45 149 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 45 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 149 (accept_3_2 28 45 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 149 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 45 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 45 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 149 (accept_3_2 25 45 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  45 149 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 45 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 45 149 (Polychromatic418967fa.accept_17_6_11_13_1_4180 23 45 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 149 (accept_3_2 22 45 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 149 (Polychromatic418967fa.accept_10_1_5_9_1_157 21 45 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 45 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 45 149 (accept_3_2 19 45 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  45 149 (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 45 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 45 149 (Polychromatic418967fa.accept_16_1_13_5_1_2280 17 45 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 149 (accept_3_2 16 45 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 149 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 45 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 45 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 149 (accept_3_2 13 45 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  45 149 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 45 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 45 149 (Polychromatic418967fa.accept_10_1_5_9_1_157 11 45 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 149 (accept_3_2 10 45 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 149 (Polychromatic418967fa.accept_16_9_13_5_1_2238 9 45 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 45 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 149 (accept_3_2 7 45 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45
  149 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 45 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 149 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 45 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 149 (accept_3_2 4 45 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 45 149 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 45 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 45
  149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 149 (accept_3_2 1 45 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 149))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  149 (allA_succ_of_accept 43 44 149 (accept_3_2 43 44 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 44 149 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 44 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 44 149 (Polychromatic418967fa.accept_8_1_4_5_1_48 41 44 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 149 (accept_3_2 40 44 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 44 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 44 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 149
  (Polychromatic418967fa.accept_9_2_8_5_1_228 38 44 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 44 149 (accept_3_2 37 44 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  44 149 (Polychromatic418967fa.accept_13_10_5_6_1_1671 36 44 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 44 149 (Polychromatic418967fa.accept_10_5_4_9_1_420 35 44 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 149 (accept_3_2 34 44 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 44 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 44 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 44 149
  (Polychromatic418967fa.accept_14_4_2_9_1_2092 32 44 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 44 149 (accept_3_2 31 44 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  44 149 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 44 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 44 149 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 44 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 44 149 (accept_3_2 28 44 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 44 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 44 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 44 149
  (Polychromatic418967fa.accept_12_2_8_5_1_408 26 44 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 44 149 (accept_3_2 25 44 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  44 149 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 44 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 44 149 (Polychromatic418967fa.accept_10_3_4_9_1_15 23 44 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 44 149 (accept_3_2 22 44 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 44 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 44 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 44 149
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 44 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 44 149 (accept_3_2 19 44 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  44 149 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 44 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 44 149 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 44 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 44 149 (accept_3_2 16 44 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 44 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 44 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 44 149
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 44 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 44 149 (accept_3_2 13 44 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  44 149 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 44 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 44 149 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 44 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 44 149 (accept_3_2 10 44 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 44 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 44 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 44 149
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 44 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 44 149 (accept_3_2 7 44 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 44
  149 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 44 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 44 149 (Polychromatic418967fa.accept_10_5_4_9_1_420 5 44 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 44 149 (accept_3_2 4 44 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 44 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 44 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 44 149 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  44 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 149 (accept_3_2 1 44 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44 149)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43
  149 (allA_of_3_0 43 43 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 149 (allA_succ_of_accept 41 42 149
  (Polychromatic418967fa.accept_10_1_2_9_1_152 41 42 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 42 149 (accept_3_2 40 42 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  42 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 42 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 42 149 (Polychromatic418967fa.accept_9_2_6_5_1_227 38 42 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 149 (accept_3_2 37 42 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 149 (Polychromatic418967fa.accept_11_3_9_6_1_105 36 42 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 42 149
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 42 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 42 149 (accept_3_2 34 42 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  42 149 (Polychromatic418967fa.accept_18_15_6_5_1_3972 33 42 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 42 149 (Polychromatic418967fa.accept_15_2_12_14_1_1709 32 42 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 149 (accept_3_2 31 42 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 42 149 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 42 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 42 149
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 42 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 42 149 (accept_3_2 28 42 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  42 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 42 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 42 149 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 42 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 149 (accept_3_2 25 42 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 149 (Polychromatic418967fa.accept_15_9_12_14_1_963 24 42 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 42 149
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 42 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 42 149 (accept_3_2 22 42 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  42 149 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 42 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 42 149 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 42 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 149 (accept_3_2 19 42 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 42 149 (Polychromatic418967fa.accept_13_5_3_6_1_3278 18 42 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 42 149
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 42 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 42 149 (accept_3_2 16 42 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  42 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 42 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 42 149 (Polychromatic418967fa.accept_11_3_9_6_1_105 14 42 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 149 (accept_3_2 13 42 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 149 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 42 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 42 149
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 42 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 42 149 (accept_3_2 10 42 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  42 149 (Polychromatic418967fa.accept_13_9_3_6_1_1661 9 42 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 42 149 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 42 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 149 (accept_3_2 7 42 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 42 149 (Polychromatic418967fa.accept_24_6_18_5_1_7949 6 42 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 42 149
  (Polychromatic418967fa.accept_13_5_3_6_1_3278 5 42 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 42 149 (accept_3_2 4 42 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 42
  149 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 42 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 42 149 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 42 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 149 (accept_3_2 1 42 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 42 149)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 149 (allA_succ_of_accept 40 41
  149 (accept_3_2 40 41 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 149
  (Polychromatic418967fa.accept_7_4_6_2_1_451 39 41 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 149 (Polychromatic418967fa.accept_7_3_6_2_1_90 38 41 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 149 (accept_3_2 37 41 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 149 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 41 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 149 (Polychromatic418967fa.accept_10_5_1_9_1_791
  35 41 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 149 (accept_3_2 34
  41 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 149
  (Polychromatic418967fa.accept_15_3_11_14_1_1705 33 41 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 41 149 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 41 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 149 (accept_3_2 31 41 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 41 149 (Polychromatic418967fa.accept_13_4_2_6_1_1043 30 41 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 149 (Polychromatic418967fa.accept_7_1_6_2_1_18 29
  41 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 149 (accept_3_2 28 41
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 41 149
  (Polychromatic418967fa.accept_13_1_2_6_1_515 27 41 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 41 149 (Polychromatic418967fa.accept_21_5_20_2_1_7948 26 41 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 149 (accept_3_2 25 41 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 41 149 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 41 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 149 (Polychromatic418967fa.accept_13_10_2_6_1_1044
  23 41 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 149 (accept_3_2 22
  41 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 41 149
  (Polychromatic418967fa.accept_13_8_2_6_1_2385 21 41 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 41 149 (Polychromatic418967fa.accept_8_4_1_5_1_186 20 41 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 149 (accept_3_2 19 41 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 41 149 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 41 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 149 (Polychromatic418967fa.accept_7_3_6_2_1_90 17
  41 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 149 (accept_3_2 16 41
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 149 (Polychromatic418967fa.accept_7_1_6_2_1_18
  15 41 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 149
  (Polychromatic418967fa.accept_11_3_8_6_1_788 14 41 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 41 149 (accept_3_2 13 41 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  41 149 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 41 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 41 149 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 41 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 149 (accept_3_2 10 41 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 41 149 (Polychromatic418967fa.accept_13_9_2_6_1_514 9 41 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 149
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 41 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 41 149 (accept_3_2 7 41 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41
  149 (Polychromatic418967fa.accept_17_6_7_13_1_3062 6 41 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 41 149 (Polychromatic418967fa.accept_10_5_1_9_1_791 5 41 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 149 (accept_3_2 4 41 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 41 149 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 41 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 149
  (Polychromatic418967fa.accept_10_2_1_9_1_1248 2 41 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 41 149 (accept_3_2 1 41 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41
  149))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 149 (allA_of_3_0 40 40 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 39 149 (allA_succ_of_accept 38 39 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 39 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 149 (accept_3_2 37 39 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 39 149 (Polychromatic418967fa.accept_15_6_9_14_1_3457
  36 39 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 39 149
  (Polychromatic418967fa.accept_9_8_3_5_1_241 35 39 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 39 149 (accept_3_2 34 39 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  39 149 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 39 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 39 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 39 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 149 (accept_3_2 31 39 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 39 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 39 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 39 149
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 39 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 39 149 (accept_3_2 28 39 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  39 149 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 39 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 39 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 39 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 149 (accept_3_2 25 39 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 39 149 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 39 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 39 149
  (Polychromatic418967fa.accept_15_8_9_14_1_4577 23 39 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 39 149 (accept_3_2 22 39 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  39 149 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 39 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 39 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 39 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 149 (accept_3_2 19 39 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 39 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 39 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 39 149
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 39 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 39 149 (accept_3_2 16 39 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  39 149 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 39 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 39 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 39 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 149 (accept_3_2 13 39 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 39 149 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 39 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 39 149
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 39 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 39 149 (accept_3_2 10 39 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  39 149 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 39 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 39 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 39 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 149 (accept_3_2 7 39 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 39 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 39 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 39 149
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 39 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 39 149 (accept_3_2 4 39 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 39
  149 (Polychromatic418967fa.accept_19_3_1_16_1_7947 3 39 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 39 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 39 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 149 (accept_3_2 1 39 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 39 149))))))))))))))))))))))))))))))))))))))) (allB_succ 38 149 (allA_succ_of_accept 37
  38 149 (accept_3_2 37 38 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 38 149
  (Polychromatic418967fa.accept_7_1_3_2_1_13 36 38 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 38 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 38 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 149 (accept_3_2 34 38 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 38 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 38 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 149 (Polychromatic418967fa.accept_11_10_5_6_1_1842
  32 38 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 38 149 (accept_3_2 31
  38 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 38 149
  (Polychromatic418967fa.accept_9_3_2_5_1_234 30 38 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 38 149 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 38 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 149 (accept_3_2 28 38 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 38 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 38 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 149 (Polychromatic418967fa.accept_7_5_3_2_1_249 26
  38 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 38 149 (accept_3_2 25 38
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 38 149
  (Polychromatic418967fa.accept_9_6_2_5_1_506 24 38 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 38 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 38 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 149 (accept_3_2 22 38 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 38 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 38 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 149 (Polychromatic418967fa.accept_7_6_3_2_1_461 20
  38 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 38 149 (accept_3_2 19 38
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 38 149
  (Polychromatic418967fa.accept_13_5_12_6_1_508 18 38 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 38 149 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 38 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 149 (accept_3_2 16 38 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 38 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 38 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 149 (Polychromatic418967fa.accept_10_4_8_9_1_784
  14 38 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 38 149 (accept_3_2 13
  38 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 38 149
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 38 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 38 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 38 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 149 (accept_3_2 10 38 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 38 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 38 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 149 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 38
  149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 38 149 (accept_3_2 7 38 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38 149 (Polychromatic418967fa.accept_7_6_3_2_1_461 6
  38 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 38 149
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 38 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 38 149 (accept_3_2 4 38 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 38
  149 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 38 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 38 149 (Polychromatic418967fa.accept_13_2_12_6_1_2394 2 38 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 149 (accept_3_2 1 38 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 38 149)))))))))))))))))))))))))))))))))))))) (allB_succ 37 149 (allA_of_3_0 37 37 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 36 149 (allA_succ_of_accept 35 36 149
  (Polychromatic418967fa.accept_10_5_6_9_1_2235 35 36 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 36 149 (accept_3_2 34 36 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  36 149 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 36 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 36 149 (Polychromatic418967fa.accept_17_15_2_13_1_4153 32 36 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 149 (accept_3_2 31 36 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 36 149 (Polychromatic418967fa.accept_11_8_3_6_1_1855 30 36 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 36 149
  (Polychromatic418967fa.accept_13_3_10_6_1_2382 29 36 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 36 149 (accept_3_2 28 36 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  36 149 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 36 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 36 149 (Polychromatic418967fa.accept_19_7_17_16_1_6478 26 36 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 149 (accept_3_2 25 36 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 36 149 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 36 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 36 149
  (Polychromatic418967fa.accept_10_3_6_9_1_779 23 36 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 36 149 (accept_3_2 22 36 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  36 149 (Polychromatic418967fa.accept_19_2_17_16_1_6481 21 36 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 36 149 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 36 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 149 (accept_3_2 19 36 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 149 (Polychromatic418967fa.accept_13_5_10_6_1_2361 18 36 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 36 149
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 36 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 36 149 (accept_3_2 16 36 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  36 149 (Polychromatic418967fa.accept_10_5_6_9_1_2235 15 36 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 36 149 (Polychromatic418967fa.accept_19_14_17_16_1_1434 14 36 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 149 (accept_3_2 13 36 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 36 149 (Polychromatic418967fa.accept_13_12_10_6_1_3212 12 36
  149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 36 149
  (Polychromatic418967fa.accept_27_11_9_14_1_7946 11 36 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 36 149 (accept_3_2 10 36 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  36 149 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 36 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 36 149 (Polychromatic418967fa.accept_11_8_3_6_1_1855 8 36 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 149 (accept_3_2 7 36 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 36 149 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 36 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 36 149
  (Polychromatic418967fa.accept_10_5_6_9_1_2235 5 36 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 36 149 (accept_3_2 4 36 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 36
  149 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 36 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 36 149 (Polychromatic418967fa.accept_13_2_10_6_1_1676 2 36 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 149 (accept_3_2 1 36 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 36 149)))))))))))))))))))))))))))))))))))) (allB_succ 35 149 (allA_succ_of_accept 34 35 149
  (accept_3_2 34 35 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 149
  (Polychromatic418967fa.accept_9_6_8_5_1_837 33 35 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 149 (Polychromatic418967fa.accept_15_2_5_14_1_61 32 35 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 149 (accept_3_2 31 35 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 35 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 35 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 149 (Polychromatic418967fa.accept_9_2_8_5_1_228 29
  35 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 149 (accept_3_2 28 35
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 149
  (Polychromatic418967fa.accept_13_1_9_6_1_146 27 35 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 35 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 35 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 149 (accept_3_2 25 35 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 35 149 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 35 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 149 (Polychromatic418967fa.accept_13_10_9_6_1_1026
  23 35 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 149 (accept_3_2 22
  35 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 149
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 35 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 35 149 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 35 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 35 149 (accept_3_2 19 35 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 35 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 35 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 149 (Polychromatic418967fa.accept_13_4_9_6_1_2376
  17 35 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 149 (accept_3_2 16
  35 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 149
  (Polychromatic418967fa.accept_9_6_8_5_1_837 15 35 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 35 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 35 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 149 (accept_3_2 13 35 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 35 149 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 35 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 149 (Polychromatic418967fa.accept_9_2_8_5_1_228 11
  35 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 149 (accept_3_2 10 35
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 35 149
  (Polychromatic418967fa.accept_15_9_5_14_1_973 9 35 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 35 149 (Polychromatic418967fa.accept_15_8_5_14_1_986 8 35 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 149 (accept_3_2 7 35 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 35 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 35 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 149 (Polychromatic418967fa.accept_14_5_7_9_1_3828 5
  35 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 149 (accept_3_2 4 35 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 149 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 35
  149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 149
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 35 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 35 149 (accept_3_2 1 35 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35
  149))))))))))))))))))))))))))))))))))) (allB_succ 34 149 (allA_of_3_0 34 34 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 33 149 (allA_succ_of_accept 32 33 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 33 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 149 (accept_3_2 31 33 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 149 (Polychromatic418967fa.accept_9_3_6_5_1_63 30
  33 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 149
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 33 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 33 149 (accept_3_2 28 33 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  33 149 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 33 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 33 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 33 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 149 (accept_3_2 25 33 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 33 149 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 33 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 149
  (Polychromatic418967fa.accept_25_23_8_24_1_7945 23 33 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 33 149 (accept_3_2 22 33 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  33 149 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 33 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 33 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 33 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 149 (accept_3_2 19 33 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 149 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 33 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 149
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 33 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 149 (accept_3_2 16 33 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  33 149 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 33 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 33 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 33 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 149 (accept_3_2 13 33 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 149 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 33 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 149
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 33 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 33 149 (accept_3_2 10 33 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  33 149 (Polychromatic418967fa.accept_13_9_7_6_1_1673 9 33 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 33 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 33 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 149 (accept_3_2 7 33 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 149 (Polychromatic418967fa.accept_10_6_3_9_1_1207 6 33 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 149
  (Polychromatic418967fa.accept_19_5_14_16_1_7944 5 33 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 33 149 (accept_3_2 4 33 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33
  149 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 33 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 33 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 33 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 149 (accept_3_2 1 33 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 33 149))))))))))))))))))))))))))))))))) (allB_succ 32 149 (allA_succ_of_accept 31 32 149
  (accept_3_2 31 32 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 32 149
  (Polychromatic418967fa.accept_14_2_4_9_1_2121 30 32 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 32 149 (Polychromatic418967fa.accept_18_11_14_5_1_3951 29 32 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 149 (accept_3_2 28 32 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 32 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 32 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 149 (Polychromatic418967fa.accept_7_5_4_2_1_235 26
  32 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 32 149 (accept_3_2 25 32
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 32 149
  (Polychromatic418967fa.accept_26_24_6_19_1_7943 24 32 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 32 149 (Polychromatic418967fa.accept_20_3_12_9_1_6410 23 32 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 149 (accept_3_2 22 32 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 32 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 32 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 149 (Polychromatic418967fa.accept_7_6_4_2_1_236 20
  32 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 32 149 (accept_3_2 19 32
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 32 149
  (Polychromatic418967fa.accept_15_3_2_14_1_1713 18 32 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 32 149 (Polychromatic418967fa.accept_10_7_2_9_1_775 17 32 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 32 149 (accept_3_2 16 32 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 32 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 32 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 32 149 (Polychromatic418967fa.accept_12_2_8_5_1_408
  14 32 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 32 149 (accept_3_2 13
  32 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 32 149
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 32 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 32 149 (Polychromatic418967fa.accept_10_1_2_9_1_152 11 32 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 149 (accept_3_2 10 32 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 32 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 32 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 149 (Polychromatic418967fa.accept_17_8_15_13_1_7942
  8 32 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 32 149 (accept_3_2 7 32
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32 149 (Polychromatic418967fa.accept_7_6_4_2_1_236
  6 32 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 32 149
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 32 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 32 149 (accept_3_2 4 32 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 32
  149 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 32 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 32 149 (Polychromatic418967fa.accept_12_2_8_5_1_408 2 32 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 149 (accept_3_2 1 32 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 32 149)))))))))))))))))))))))))))))))) (allB_succ 31 149 (allA_of_3_0 31 31 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 30 149 (allA_succ_of_accept 29 30 149
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 30 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 30 149 (accept_3_2 28 30 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  30 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 30 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 30 149 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 30 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 30 149 (accept_3_2 25 30 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 30 149 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 30 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 30 149
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 30 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 30 149 (accept_3_2 22 30 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  30 149 (Polychromatic418967fa.accept_14_7_2_9_1_2093 21 30 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 30 149 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 30 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 149 (accept_3_2 19 30 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 149 (Polychromatic418967fa.accept_13_5_4_6_1_2371 18 30 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 30 149
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 30 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 30 149 (accept_3_2 16 30 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  30 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 30 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 30 149 (Polychromatic418967fa.accept_11_3_8_6_1_788 14 30 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 149 (accept_3_2 13 30 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 149 (Polychromatic418967fa.accept_21_12_9_2_1_7941 12 30 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 30 149
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 30 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 30 149 (accept_3_2 10 30 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  30 149 (Polychromatic418967fa.accept_13_9_4_6_1_1005 9 30 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 30 149 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 30 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 149 (accept_3_2 7 30 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 30 149 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 30 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 30 149
  (Polychromatic418967fa.accept_13_5_4_6_1_2371 5 30 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 30 149 (accept_3_2 4 30 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 30
  149 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 30 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 30 149 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 30 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 149 (accept_3_2 1 30 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 30 149)))))))))))))))))))))))))))))) (allB_succ 29 149 (allA_succ_of_accept 28 29 149
  (accept_3_2 28 29 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 149
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 29 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 149 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 29 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 149 (accept_3_2 25 29 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 149 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 29 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 149 (Polychromatic418967fa.accept_11_1_7_6_1_378
  23 29 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 149 (accept_3_2 22
  29 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 149
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 29 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 29 149 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 29 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 149 (accept_3_2 19 29 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 29 149 (Polychromatic418967fa.accept_13_5_3_6_1_3278 18 29 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 149 (Polychromatic418967fa.accept_7_3_1_2_1_247 17
  29 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 149 (accept_3_2 16 29
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 149
  (Polychromatic418967fa.accept_9_6_2_5_1_506 15 29 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 29 149 (Polychromatic418967fa.accept_13_1_3_6_1_158 14 29 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 149 (accept_3_2 13 29 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 29 149 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 29 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 149
  (Polychromatic418967fa.accept_17_11_12_13_1_3030 11 29 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 29 149 (accept_3_2 10 29 149 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 29 149 (Polychromatic418967fa.accept_13_9_3_6_1_1661 9 29 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 149 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 29 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 149 (accept_3_2 7 29 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 149 (Polychromatic418967fa.accept_7_6_1_2_1_230 6
  29 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 149
  (Polychromatic418967fa.accept_13_5_3_6_1_3278 5 29 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 149 (accept_3_2 4 29 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  149 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 29 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 149 (Polychromatic418967fa.accept_16_2_13_5_1_2257 2 29 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 149 (accept_3_2 1 29 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 149))))))))))))))))))))))))))))) (allB_succ 28 149 (allA_of_3_0 28 28 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 27 149 (allA_succ_of_accept 26 27 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 27
  149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 149 (accept_3_2 25 27 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 149 (Polychromatic418967fa.accept_7_3_6_2_1_90 24
  27 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 149
  (Polychromatic418967fa.accept_11_1_5_6_1_397 23 27 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 27 149 (accept_3_2 22 27 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  27 149 (Polychromatic418967fa.accept_11_10_5_6_1_1842 21 27 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 27 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 27 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 149 (accept_3_2 19 27 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 27 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 27 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 149
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 27 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 27 149 (accept_3_2 16 27 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  27 149 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 27 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 27 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 27 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 149 (accept_3_2 13 27 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 27 149 (Polychromatic418967fa.accept_10_2_7_9_1_783 12 27 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 149
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 27 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 27 149 (accept_3_2 10 27 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  27 149 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 27 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 27 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 27 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 149 (accept_3_2 7 27 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 27 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 27 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 149
  (Polychromatic418967fa.accept_13_5_1_6_1_2367 5 27 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 27 149 (accept_3_2 4 27 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27
  149 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 27 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 27 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 27 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 149 (accept_3_2 1 27 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 27 149))))))))))))))))))))))))))) (allB_succ 26 149 (allA_succ_of_accept 25 26 149 (accept_3_2
  25 26 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 26 149
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 26 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 26 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 26 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 26 149 (accept_3_2 22 26 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 26 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 26 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 26 149 (Polychromatic418967fa.accept_9_2_8_5_1_228 20
  26 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 26 149 (accept_3_2 19 26
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 26 149
  (Polychromatic418967fa.accept_7_4_5_2_1_243 18 26 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 26 149 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 26 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 26 149 (accept_3_2 16 26 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 26 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 26 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 26 149
  (Polychromatic418967fa.accept_16_14_10_5_1_1393 14 26 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 26 149 (accept_3_2 13 26 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  26 149 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 26 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 26 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 26 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 26 149 (accept_3_2 10 26 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 26 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 26 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 26 149
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 26 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 26 149 (accept_3_2 7 26 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 26
  149 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 26 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 26 149 (Polychromatic418967fa.accept_10_5_6_9_1_2235 5 26 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 26 149 (accept_3_2 4 26 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 26 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 26 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 26 149 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  26 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 26 149 (accept_3_2 1 26 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26 149)))))))))))))))))))))))))) (allB_succ 25 149 (allA_of_3_0 25
  25 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 24 149 (allA_succ_of_accept 23 24 149
  (Polychromatic418967fa.accept_10_3_4_9_1_15 23 24 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 24 149 (accept_3_2 22 24 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  24 149 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 24 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 24 149 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 24 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 24 149 (accept_3_2 19 24 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 24 149 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 24 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 24 149
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 24 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 24 149 (accept_3_2 16 24 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  24 149 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 24 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 24 149 (Polychromatic418967fa.accept_19_14_5_16_1_7940 14 24 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 149 (accept_3_2 13 24 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 24 149 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 24 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 24 149
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 24 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 24 149 (accept_3_2 10 24 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  24 149 (Polychromatic418967fa.accept_21_9_3_2_1_6363 9 24 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 24 149 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 24 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 149 (accept_3_2 7 24 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 24 149 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 24 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 24 149
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 24 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 24 149 (accept_3_2 4 24 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 24
  149 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 24 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 24 149 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 24 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 24 149 (accept_3_2 1 24 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 24 149)))))))))))))))))))))))) (allB_succ 23 149 (allA_succ_of_accept 22 23 149 (accept_3_2 22
  23 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 149
  (Polychromatic418967fa.accept_15_6_8_14_1_4575 21 23 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 149 (Polychromatic418967fa.accept_15_5_8_14_1_432 20 23 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 149 (accept_3_2 19 23 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 23 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 149 (Polychromatic418967fa.accept_13_4_10_6_1_989
  17 23 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 149 (accept_3_2 16
  23 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 149
  (Polychromatic418967fa.accept_13_2_10_6_1_1676 15 23 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 23 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 23 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 149 (accept_3_2 13 23 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 23 149 (Polychromatic418967fa.accept_13_12_10_6_1_3212 12 23 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 149
  (Polychromatic418967fa.accept_16_11_7_5_1_4364 11 23 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 23 149 (accept_3_2 10 23 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  23 149 (Polychromatic418967fa.accept_13_9_10_6_1_1028 9 23 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 23 149 (Polychromatic418967fa.accept_24_8_23_5_1_7939 8 23 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 149 (accept_3_2 7 23 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 23 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 23 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 149
  (Polychromatic418967fa.accept_11_5_1_6_1_774 5 23 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 23 149 (accept_3_2 4 23 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23
  149 (Polychromatic418967fa.accept_13_3_10_6_1_2382 3 23 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 23 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 23 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 149 (accept_3_2 1 23 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 23 149))))))))))))))))))))))) (allB_succ 22 149 (allA_of_3_0 22 22 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 21 149 (allA_succ_of_accept 20 21 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 21 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 149 (accept_3_2 19 21 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  21 149 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 21 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 21 149 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 21 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 149 (accept_3_2 16 21 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 149 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 21 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 21 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 21 149 (accept_3_2 13 21 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  21 149 (Polychromatic418967fa.accept_10_2_1_9_1_1248 12 21 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 21 149 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 21 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 149 (accept_3_2 10 21 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 149 (Polychromatic418967fa.accept_15_9_6_14_1_2627 9 21 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 21 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 149 (accept_3_2 7 21 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21
  149 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 21 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 149 (Polychromatic418967fa.accept_10_5_1_9_1_791 5 21 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 149 (accept_3_2 4 21 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 21 149 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 21 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 21
  149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 149 (accept_3_2 1 21 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 149))))))))))))))))))))) (allB_succ 20 149 (allA_succ_of_accept
  19 20 149 (accept_3_2 19 20 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 20 149
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 20 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 20 149 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 20 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 149 (accept_3_2 16 20 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 20 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 20 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 20 149 (Polychromatic418967fa.accept_11_3_9_6_1_105
  14 20 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 20 149 (accept_3_2 13
  20 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 20 149
  (Polychromatic418967fa.accept_9_3_2_5_1_234 12 20 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 20 149 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 20 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 20 149 (accept_3_2 10 20 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 20 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 20 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 149 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 20
  149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 20 149 (accept_3_2 7 20 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20 149 (Polychromatic418967fa.accept_9_6_2_5_1_506 6
  20 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 20 149
  (Polychromatic418967fa.accept_19_5_1_16_1_6501 5 20 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 20 149 (accept_3_2 4 20 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 20
  149 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 20 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 20 149 (Polychromatic418967fa.accept_12_2_8_5_1_408 2 20 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 20 149 (accept_3_2 1 20 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 149)))))))))))))))))))) (allB_succ 19 149 (allA_of_3_0 19 19 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 18 149 (allA_succ_of_accept 17 18 149 (Polychromatic418967fa.accept_10_7_8_9_1_785 17 18 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 149 (accept_3_2 16 18 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 18 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 15
  18 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 149
  (Polychromatic418967fa.accept_10_4_8_9_1_784 14 18 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 18 149 (accept_3_2 13 18 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  18 149 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 18 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 18 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 18 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 149 (accept_3_2 10 18 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 18 149 (Polychromatic418967fa.accept_19_9_18_16_1_7938 9 18 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 149
  (Polychromatic418967fa.accept_19_8_18_16_1_7937 8 18 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 18 149 (accept_3_2 7 18 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18
  149 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 18 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 18 149 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 18 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 149 (accept_3_2 4 18 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 18 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 18 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 18 149 (Polychromatic418967fa.accept_14_2_4_9_1_2121 2
  18 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 149 (accept_3_2 1 18 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 149)))))))))))))))))) (allB_succ 17 149 (allA_succ_of_accept 16
  17 149 (accept_3_2 16 17 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 149
  (Polychromatic418967fa.accept_7_1_3_2_1_13 15 17 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 17 149 (Polychromatic418967fa.accept_19_14_17_16_1_1434 14 17 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 149 (accept_3_2 13 17 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 17 149 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 17 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 149 (Polychromatic418967fa.accept_9_2_8_5_1_228 11
  17 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 149 (accept_3_2 10 17
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 149
  (Polychromatic418967fa.accept_13_9_4_6_1_1005 9 17 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 17 149 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 17 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 149 (accept_3_2 7 17 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 17 149 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 17 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 149 (Polychromatic418967fa.accept_7_5_3_2_1_249 5
  17 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 149 (accept_3_2 4 17 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17 149 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 17
  149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 149
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 17 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 17 149 (accept_3_2 1 17 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17
  149))))))))))))))))) (allB_succ 16 149 (allA_of_3_0 16 16 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15
  149 (allA_succ_of_accept 14 15 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 15 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 149 (accept_3_2 13 15 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 15 149 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 15 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 149 (Polychromatic418967fa.accept_9_2_6_5_1_227 11
  15 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 149 (accept_3_2 10 15
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 149
  (Polychromatic418967fa.accept_12_9_3_5_1_423 9 15 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 15 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 15 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 149 (accept_3_2 7 15 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 15 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 15 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 15 149 (Polychromatic418967fa.accept_17_5_15_13_1_7936
  5 15 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 149 (accept_3_2 4 15
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 15 149 (Polychromatic418967fa.accept_7_3_1_2_1_247
  3 15 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 149
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 15 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 15 149 (accept_3_2 1 15 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15
  149))))))))))))))) (allB_succ 14 149 (allA_succ_of_accept 13 14 149 (accept_3_2 13 14 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 14 149 (Polychromatic418967fa.accept_19_12_14_16_1_7935 12 14 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 14 149
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 14 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 14 149 (accept_3_2 10 14 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  14 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 14 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 14 149 (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 14 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 14 149 (accept_3_2 7 14 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 14 149 (Polychromatic418967fa.accept_20_6_14_9_1_3489 6 14 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 14 149
  (Polychromatic418967fa.accept_10_5_4_9_1_420 5 14 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 14 149 (accept_3_2 4 14 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 14
  149 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 14 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 14 149 (Polychromatic418967fa.accept_13_2_1_6_1_2365 2 14 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 14 149 (accept_3_2 1 14 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 14 149)))))))))))))) (allB_succ 13 149 (allA_of_3_0 13 13 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 12 149 (allA_succ_of_accept 11 12 149 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 12 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 149 (accept_3_2 10 12 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 12 149 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 12
  149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 149
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 12 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 12 149 (accept_3_2 7 12 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12
  149 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 12 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 12 149 (Polychromatic418967fa.accept_11_5_1_6_1_774 5 12 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 149 (accept_3_2 4 12 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 12 149 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 12 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 12 149 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 12
  149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12 149 (accept_3_2 1 12 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 149)))))))))))) (allB_succ 11 149 (allA_succ_of_accept 10 11 149
  (accept_3_2 10 11 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 149
  (Polychromatic418967fa.accept_16_9_11_5_1_2279 9 11 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 149 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 11 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 149 (accept_3_2 7 11 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 11 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 149 (Polychromatic418967fa.accept_7_5_4_2_1_235 5
  11 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 149 (accept_3_2 4 11 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 149 (Polychromatic418967fa.accept_9_3_2_5_1_234 3
  11 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 149
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 11 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 149 (accept_3_2 1 11 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  149))))))))))) (allB_succ 10 149 (allA_of_3_0 10 10 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 9 149
  (allA_succ_of_accept 8 9 149 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 9 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 149 (accept_3_2 7 9 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 9 149 (Polychromatic418967fa.accept_15_6_9_14_1_3457 6 9 149 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 149 (Polychromatic418967fa.accept_15_5_9_14_1_1724 5
  9 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 149 (accept_3_2 4 9 149
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 149 (Polychromatic418967fa.accept_11_3_9_6_1_105 3 9
  149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 149
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 9 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 9 149 (accept_3_2 1 9 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 149)))))))))
  (allB_succ 8 149 (allA_succ_of_accept 7 8 149 (accept_3_2 7 8 149 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 8 149 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 8 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 8 149 (Polychromatic418967fa.accept_15_5_8_14_1_432 5 8 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 8 149 (accept_3_2 4 8 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 8 149 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 8 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 8 149
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 8 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 8 149 (accept_3_2 1 8 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 149))))))))
  (allB_succ 7 149 (allA_of_3_0 7 7 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 6 149 (allA_succ_of_accept 5
  6 149 (Polychromatic418967fa.accept_10_5_6_9_1_2235 5 6 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 6 149 (accept_3_2 4 6 149 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 6 149 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 6 149 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 6 149 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 6 149
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 149 (accept_3_2 1 6 149 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 6 149)))))) (allB_succ 5 149 (allA_succ_of_accept 4 5 149 (accept_3_2 4 5
  149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 149 (Polychromatic418967fa.accept_7_3_5_2_1_17 3
  5 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 149
  (Polychromatic418967fa.accept_15_2_5_14_1_61 2 5 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 5 149 (accept_3_2 1 5 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 149)))))
  (allB_succ 4 149 (allA_of_3_0 4 4 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 3 149 (allA_succ_of_accept 2
  3 149 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 3 149 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 3 149 (accept_3_2 1 3 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 149)))
  (allB_succ 2 149 (allA_succ_of_accept 1 2 149 (accept_3_2 1 2 149 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2
  149)) (allB_two
  149)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


