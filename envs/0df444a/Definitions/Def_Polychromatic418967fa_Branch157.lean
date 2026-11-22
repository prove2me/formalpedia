-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch157
-- name    : Polychromatic418967fa_Branch157
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:17:17.838171+00:00
-- url     : https://prove2.me/theorems/c84cba09-f198-4aa2-acb8-efb43c757ce9
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

def Polychromatic418967fa.branch_157 : allB 157 157 :=
  allB_succ' 2 156 157 (Eq.refl Bool.true) (allA_succ_of_accept 1 156 157 (Polychromatic418967fa.accept_7_1_2_3_1_257 1
  156 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156 157)) (allB_succ' 3 155 157
  (Eq.refl Bool.true) (allA_of_3_1 3 155 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 154 157 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 154 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 154 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 154 157 (accept_3_3 2 154 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 154 157 (Polychromatic418967fa.accept_10_1_4_7_1_374 1 154 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 154 157)))) (allB_succ' 5 153 157 (Eq.refl Bool.true)
  (allA_succ_of_accept 4 153 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 153 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 153 157 (Polychromatic418967fa.accept_12_3_9_1_1_290 3 153 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 153 157 (accept_3_3 2 153 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 157 (Polychromatic418967fa.accept_16_1_9_13_1_1822
  1 153 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 153 157))))) (allB_succ' 6 152 157
  (Eq.refl Bool.true) (allA_of_3_1 6 152 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 151 157 (Eq.refl
  Bool.true) (allA_succ_of_accept 6 151 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 151 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 151 157 (accept_3_3 5 151 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 151 157 (Polychromatic418967fa.accept_10_4_1_7_1_371 4 151 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 151 157
  (Polychromatic418967fa.accept_9_3_7_4_1_53 3 151 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 151 157 (accept_3_3 2 151 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  151 157 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 151 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 151 157))))))) (allB_succ' 8 150 157 (Eq.refl Bool.true) (allA_succ_of_accept 7 150 157
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 150 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 150 157 (Polychromatic418967fa.accept_13_6_7_1_1_335 6 150 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 150 157 (accept_3_3 5 150 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 150 157 (Polychromatic418967fa.accept_11_4_7_3_1_289 4 150 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 150 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 3
  150 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 150 157 (accept_3_3 2 150
  157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 150 157 (Polychromatic418967fa.accept_9_1_6_4_1_49
  1 150 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150 157)))))))) (allB_succ' 9 149 157
  (Eq.refl Bool.true) (allA_of_3_1 9 149 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 148 157 (Eq.refl
  Bool.true) (allA_succ_of_accept 9 148 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 148 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 148 157 (accept_3_3 8 148 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 148 157 (Polychromatic418967fa.accept_16_7_4_13_1_1057 7 148 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 148 157
  (Polychromatic418967fa.accept_13_6_5_1_1_834 6 148 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 148 157 (accept_3_3 5 148 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  148 157 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 148 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 148 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 148 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 148 157 (accept_3_3 2 148 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 148 157 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 148 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 148 157)))))))))) (allB_succ' 11 147 157 (Eq.refl
  Bool.true) (allA_succ_of_accept 10 147 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 147 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 147 157 (Polychromatic418967fa.accept_12_9_3_1_1_303 9
  147 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 147 157 (accept_3_3 8 147
  157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 157
  (Polychromatic418967fa.accept_9_7_3_4_1_218 7 147 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 147 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 147 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 147 157 (accept_3_3 5 147 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 147 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 147 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 147 157 (Polychromatic418967fa.accept_13_3_4_1_1_363 3
  147 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 147 157 (accept_3_3 2 147
  157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 157 (Polychromatic418967fa.accept_9_1_3_4_1_47
  1 147 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 147 157))))))))))) (allB_succ' 12 146
  157 (Eq.refl Bool.true) (allA_of_3_1 12 146 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 145 157
  (Eq.refl Bool.true) (allA_succ_of_accept 12 145 157 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 145 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 145 157 (accept_3_3 11 145 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 145 157 (Polychromatic418967fa.accept_18_10_1_13_1_2192 10 145
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 145 157
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 145 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 145 157 (accept_3_3 8 145 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  145 157 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 145 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 145 157 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 145 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 145 157 (accept_3_3 5 145 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 145 157 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 145 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 145 157
  (Polychromatic418967fa.accept_9_3_1_4_1_216 3 145 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 145 157 (accept_3_3 2 145 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  145 157 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 145 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 145 157))))))))))))) (allB_succ' 14 144 157 (Eq.refl Bool.true) (allA_succ_of_accept 13 144 157
  (Polychromatic418967fa.accept_7_6_4_3_1_266 13 144 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 144 157 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 144 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 144 157 (accept_3_3 11 144 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 144 157 (Polychromatic418967fa.accept_19_10_11_5_1_7093 10 144 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 144 157
  (Polychromatic418967fa.accept_21_9_18_10_1_5388 9 144 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 144 157 (accept_3_3 8 144 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  144 157 (Polychromatic418967fa.accept_14_7_4_3_1_488 7 144 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 144 157 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 144 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 144 157 (accept_3_3 5 144 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 144 157 (Polychromatic418967fa.accept_26_4_14_1_1_8621 4 144 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 144 157
  (Polychromatic418967fa.accept_10_3_4_7_1_353 3 144 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 144 157 (accept_3_3 2 144 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  144 157 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 144 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 144 157)))))))))))))) (allB_succ' 15 143 157 (Eq.refl Bool.true) (allA_of_3_1 15 143 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 142 157 (Eq.refl Bool.true) (allA_succ_of_accept 15 142 157
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 142 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 142 157 (accept_3_3 14 142 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 142 157 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 142 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 142 157 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 142 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 142 157 (accept_3_3 11 142 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 142 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 142 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 142 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 142 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 142 157 (accept_3_3 8 142 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  142 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 142 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 142 157 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 142 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 142 157 (accept_3_3 5 142 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 142 157 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 142 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 142 157
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 142 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 142 157 (accept_3_3 2 142 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  142 157 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 142 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 142 157)))))))))))))))) (allB_succ' 17 141 157 (Eq.refl Bool.true) (allA_succ_of_accept 16 141
  157 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 141 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 141 157 (Polychromatic418967fa.accept_12_3_9_1_1_290 15 141 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 141 157 (accept_3_3 14 141 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 141 157 (Polychromatic418967fa.accept_15_13_6_7_1_1369 13 141 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 141 157
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 141 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 141 157 (accept_3_3 11 141 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 141 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 141 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 141 157 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 141 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 141 157 (accept_3_3 8 141 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 157 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 141 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 141 157
  (Polychromatic418967fa.accept_10_6_1_7_1_342 6 141 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 141 157 (accept_3_3 5 141 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  141 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 141 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 141 157 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 141 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 141 157 (accept_3_3 2 141 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 157 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 141 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 141 157))))))))))))))))) (allB_succ' 18 140 157 (Eq.refl
  Bool.true) (allA_of_3_1 18 140 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 139 157 (Eq.refl Bool.true)
  (allA_succ_of_accept 18 139 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 139 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 139 157 (accept_3_3 17 139 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 139 157 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 139 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 139 157 (Polychromatic418967fa.accept_11_4_7_3_1_289
  15 139 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 139 157 (accept_3_3 14
  139 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 139 157
  (Polychromatic418967fa.accept_17_13_3_4_1_2537 13 139 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 139 157 (Polychromatic418967fa.accept_10_2_9_7_1_720 12 139 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 139 157 (accept_3_3 11 139 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 139 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 139 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 139 157 (Polychromatic418967fa.accept_7_2_6_3_1_100 9
  139 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 139 157 (accept_3_3 8 139
  157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 139 157
  (Polychromatic418967fa.accept_17_7_3_4_1_8563 7 139 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 139 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 139 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 139 157 (accept_3_3 5 139 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 139 157 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 139 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 139 157 (Polychromatic418967fa.accept_15_3_4_7_1_1352
  3 139 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 139 157 (accept_3_3 2
  139 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 139 157
  (Polychromatic418967fa.accept_19_1_6_5_1_4319 1 139 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 139 157))))))))))))))))))) (allB_succ' 20 138 157 (Eq.refl Bool.true) (allA_succ_of_accept 19 138 157
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 138 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 138 157 (Polychromatic418967fa.accept_13_5_8_1_1_2161 18 138 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 138 157 (accept_3_3 17 138 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 138 157 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 138 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 138 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 15
  138 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 138 157 (accept_3_3 14
  138 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 138 157
  (Polychromatic418967fa.accept_29_13_22_12_1_8620 13 138 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 138 157 (Polychromatic418967fa.accept_13_12_8_1_1_825 12 138 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 138 157 (accept_3_3 11 138 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 138 157 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 138 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 138 157
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 138 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 138 157 (accept_3_3 8 138 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  138 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 138 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 138 157 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 138 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 138 157 (accept_3_3 5 138 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 138 157 (Polychromatic418967fa.accept_15_4_3_7_1_713 4 138 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 138 157
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 138 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 138 157 (accept_3_3 2 138 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  138 157 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 138 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 138 157)))))))))))))))))))) (allB_succ' 21 137 157 (Eq.refl Bool.true) (allA_of_3_1 21 137 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 136 157 (Eq.refl Bool.true) (allA_succ_of_accept 21 136 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 136 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 136 157 (accept_3_3 20 136 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 136 157 (Polychromatic418967fa.accept_16_3_8_13_1_3867 19 136 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 136 157 (Polychromatic418967fa.accept_11_7_4_3_1_302 18 136 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 136 157 (accept_3_3 17 136 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 136 157 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 136 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 136 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 136 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 136 157 (accept_3_3 14 136 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 136 157 (Polychromatic418967fa.accept_10_3_6_7_1_2188 13 136 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 136 157 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 136 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 136 157 (accept_3_3 11 136 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 136 157 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 136 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 136 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 136 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 136 157 (accept_3_3 8 136 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  136 157 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 136 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 136 157 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 136 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 136 157 (accept_3_3 5 136 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 136 157 (Polychromatic418967fa.accept_16_4_8_13_1_1059 4 136 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 136 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 136 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 136 157 (accept_3_3 2 136 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  136 157 (Polychromatic418967fa.accept_10_1_6_7_1_710 1 136 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 136 157)))))))))))))))))))))) (allB_succ' 23 135 157 (Eq.refl Bool.true) (allA_succ_of_accept 22
  135 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 135 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 135 157 (Polychromatic418967fa.accept_12_9_3_1_1_303 21 135 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 135 157 (accept_3_3 20 135 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 135 157 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 135 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 135 157
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 135 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 135 157 (accept_3_3 17 135 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 135 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 135 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 135 157 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 135 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 135 157 (accept_3_3 14 135 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 157 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 135 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 135 157
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 135 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 135 157 (accept_3_3 11 135 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 135 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 135 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 135 157 (Polychromatic418967fa.accept_12_9_3_1_1_303 9 135 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 135 157 (accept_3_3 8 135 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 157 (Polychromatic418967fa.accept_19_7_2_5_1_5680 7 135 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 135 157
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 135 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 135 157 (accept_3_3 5 135 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  135 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 135 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 135 157 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 135 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 135 157 (accept_3_3 2 135 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 157 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 135 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135 157))))))))))))))))))))))) (allB_succ' 24 134 157
  (Eq.refl Bool.true) (allA_of_3_1 24 134 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 133 157 (Eq.refl
  Bool.true) (allA_succ_of_accept 24 133 157 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 133 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 133 157 (accept_3_3 23 133 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 133 157 (Polychromatic418967fa.accept_18_4_7_13_1_3303 22 133 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 133 157
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 133 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 133 157 (accept_3_3 20 133 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 133 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 133 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 133 157 (Polychromatic418967fa.accept_13_5_3_1_1_1398 18 133 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 133 157 (accept_3_3 17 133 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 133 157 (Polychromatic418967fa.accept_10_6_3_7_1_2197 16 133
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 133 157
  (Polychromatic418967fa.accept_9_6_7_4_1_212 15 133 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 133 157 (accept_3_3 14 133 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 133 157 (Polychromatic418967fa.accept_11_2_1_3_1_683 13 133 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 133 157 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 133 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 133 157 (accept_3_3 11 133 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 133 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 133 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 133 157
  (Polychromatic418967fa.accept_15_9_13_7_1_1361 9 133 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 133 157 (accept_3_3 8 133 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  133 157 (Polychromatic418967fa.accept_13_7_3_1_1_814 7 133 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 133 157 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 133 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 133 157 (accept_3_3 5 133 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 133 157 (Polychromatic418967fa.accept_10_4_3_7_1_1110 4 133 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 133 157
  (Polychromatic418967fa.accept_9_3_7_4_1_53 3 133 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 133 157 (accept_3_3 2 133 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  133 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 133 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 133 157))))))))))))))))))))))))) (allB_succ' 26 132 157 (Eq.refl Bool.true) (allA_succ_of_accept
  25 132 157 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 132 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 132 157 (Polychromatic418967fa.accept_10_4_2_7_1_373 24 132 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 132 157 (accept_3_3 23 132 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 132 157 (Polychromatic418967fa.accept_13_9_2_1_1_813 22 132
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 132 157
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 132 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 132 157 (accept_3_3 20 132 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 132 157 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 132 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 132 157 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 132 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 132 157 (accept_3_3 17 132 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 132 157 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 132 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 132 157
  (Polychromatic418967fa.accept_10_5_2_7_1_345 15 132 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 132 157 (accept_3_3 14 132 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 132 157 (Polychromatic418967fa.accept_19_13_18_5_1_8619 13 132 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 132 157 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 132 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 132 157 (accept_3_3 11 132 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 132 157 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 132 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 132 157
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 132 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 132 157 (accept_3_3 8 132 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  132 157 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 132 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 132 157 (Polychromatic418967fa.accept_13_6_2_1_1_2137 6 132 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 132 157 (accept_3_3 5 132 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 132 157 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 132 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 132 157
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 132 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 132 157 (accept_3_3 2 132 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  132 157 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 132 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 132 157)))))))))))))))))))))))))) (allB_succ' 27 131 157 (Eq.refl Bool.true) (allA_of_3_1 27 131
  157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 130 157 (Eq.refl Bool.true) (allA_succ_of_accept 27 130
  157 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 130 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 130 157 (accept_3_3 26 130 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 130 157 (Polychromatic418967fa.accept_18_7_4_13_1_3315 25 130 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 130 157 (Polychromatic418967fa.accept_22_2_20_3_1_8618 24 130 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 130 157 (accept_3_3 23 130 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 130 157 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 130 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 130 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 130 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 130 157 (accept_3_3 20 130 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 130 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 130 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 130 157 (Polychromatic418967fa.accept_15_3_10_7_1_2196 18 130 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 130 157 (accept_3_3 17 130 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 130 157 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 130
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 130 157
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 130 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 130 157 (accept_3_3 14 130 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 130 157 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 130 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 130 157 (Polychromatic418967fa.accept_15_12_10_7_1_1357 12 130 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 130 157 (accept_3_3 11 130 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 130 157 (Polychromatic418967fa.accept_17_10_11_4_1_2522 10 130
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 130 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 130 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 130 157 (accept_3_3 8 130 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  130 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 130 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 130 157 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 130 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 130 157 (accept_3_3 5 130 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 130 157 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 130 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 130 157
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 130 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 130 157 (accept_3_3 2 130 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  130 157 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 130 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 130 157)))))))))))))))))))))))))))) (allB_succ' 29 129 157 (Eq.refl Bool.true)
  (allA_succ_of_accept 28 129 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 129 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 129 157 (Polychromatic418967fa.accept_11_5_8_3_1_66 27 129 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 129 157 (accept_3_3 26 129 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 157 (Polychromatic418967fa.accept_9_7_3_4_1_218
  25 129 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 129 157
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 129 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 129 157 (accept_3_3 23 129 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 129 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 129 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 129 157 (Polychromatic418967fa.accept_13_8_12_1_1_4662 21 129 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 129 157 (accept_3_3 20 129 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 157 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 129 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 129 157
  (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 129 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 129 157 (accept_3_3 17 129 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 129 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 129 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 129 157 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 129 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 129 157 (accept_3_3 14 129 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 157 (Polychromatic418967fa.accept_15_13_9_7_1_2194 13 129 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 129 157
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 129 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 129 157 (accept_3_3 11 129 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 129 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 129 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 129 157 (Polychromatic418967fa.accept_16_9_1_13_1_1850 9 129 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 129 157 (accept_3_3 8 129 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 157 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 129 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 129 157
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 129 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 129 157 (accept_3_3 5 129 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  129 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 129 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 129 157 (Polychromatic418967fa.accept_12_3_9_1_1_290 3 129 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 129 157 (accept_3_3 2 129 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 157 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 129 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129 157))))))))))))))))))))))))))))) (allB_succ' 30 128
  157 (Eq.refl Bool.true) (allA_of_3_1 30 128 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 127 157
  (Eq.refl Bool.true) (allA_succ_of_accept 30 127 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 127 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 127 157 (accept_3_3 29 127 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 127 157 (Polychromatic418967fa.accept_16_12_15_13_1_3872 28
  127 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 127 157
  (Polychromatic418967fa.accept_19_8_13_5_1_1889 27 127 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 127 157 (accept_3_3 26 127 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 127 157 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 127 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 127 157 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 127 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 127 157 (accept_3_3 23 127 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 127 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 127 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 127 157
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 127 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 127 157 (accept_3_3 20 127 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 127 157 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 127 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 127 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 127 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 127 157 (accept_3_3 17 127 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 127 157 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 127 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 127 157
  (Polychromatic418967fa.accept_9_6_1_4_1_474 15 127 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 127 157 (accept_3_3 14 127 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 127 157 (Polychromatic418967fa.accept_17_13_8_4_1_2514 13 127 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 127 157 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 127 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 127 157 (accept_3_3 11 127 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 127 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 127 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 127 157
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 127 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 127 157 (accept_3_3 8 127 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  127 157 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 127 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 127 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 127 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 127 157 (accept_3_3 5 127 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 127 157 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 127 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 127 157
  (Polychromatic418967fa.accept_9_3_1_4_1_216 3 127 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 127 157 (accept_3_3 2 127 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  127 157 (Polychromatic418967fa.accept_17_1_8_4_1_1519 1 127 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 127 157))))))))))))))))))))))))))))))) (allB_succ' 32 126 157 (Eq.refl Bool.true)
  (allA_succ_of_accept 31 126 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 126 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 126 157 (Polychromatic418967fa.accept_11_8_5_3_1_694 30 126
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 126 157 (accept_3_3 29 126
  157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 126 157
  (Polychromatic418967fa.accept_13_2_9_1_1_67 28 126 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 126 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 126 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 126 157 (accept_3_3 26 126 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 126 157 (Polychromatic418967fa.accept_17_8_7_4_1_8617 25 126 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 126 157
  (Polychromatic418967fa.accept_13_11_9_1_1_1407 24 126 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 126 157 (accept_3_3 23 126 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 126 157 (Polychromatic418967fa.accept_23_22_11_19_1_8616 22 126 157 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 126 157 (Polychromatic418967fa.accept_10_1_6_7_1_710 21 126 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 126 157 (accept_3_3 20 126 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 126 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 126 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 126 157
  (Polychromatic418967fa.accept_13_5_9_1_1_1405 18 126 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 126 157 (accept_3_3 17 126 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 126 157 (Polychromatic418967fa.accept_15_1_6_7_1_6282 16 126 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 126 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 126 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 126 157 (accept_3_3 14 126 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 126 157 (Polychromatic418967fa.accept_10_3_6_7_1_2188 13 126 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 126 157
  (Polychromatic418967fa.accept_15_12_6_7_1_1353 12 126 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 126 157 (accept_3_3 11 126 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 126 157 (Polychromatic418967fa.accept_13_10_9_1_1_5609 10 126 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 126 157 (Polychromatic418967fa.accept_19_9_12_5_1_5695 9 126 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 126 157 (accept_3_3 8 126 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 126 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 126 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 126 157
  (Polychromatic418967fa.accept_13_6_9_1_1_5604 6 126 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 126 157 (accept_3_3 5 126 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  126 157 (Polychromatic418967fa.accept_19_4_12_5_1_8615 4 126 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 126 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 126 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 126 157 (accept_3_3 2 126 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 126 157 (Polychromatic418967fa.accept_10_1_6_7_1_710 1 126 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126 157)))))))))))))))))))))))))))))))) (allB_succ' 33
  125 157 (Eq.refl Bool.true) (allA_of_3_1 33 125 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 124 157
  (Eq.refl Bool.true) (allA_succ_of_accept 33 124 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 124 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 124 157 (accept_3_3 32 124 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 124 157 (Polychromatic418967fa.accept_10_1_4_7_1_374 31 124
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 124 157
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 124 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 124 157 (accept_3_3 29 124 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 124 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 124 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 124 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 124 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 124 157 (accept_3_3 26 124 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 124 157 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 124 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 124 157
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 124 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 124 157 (accept_3_3 23 124 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 124 157 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 124 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 124 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 124 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 124 157 (accept_3_3 20 124 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 124 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 124 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 124 157
  (Polychromatic418967fa.accept_15_3_4_7_1_1352 18 124 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 124 157 (accept_3_3 17 124 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 124 157 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 124 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 124 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 124 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 124 157 (accept_3_3 14 124 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 124 157 (Polychromatic418967fa.accept_10_3_4_7_1_353 13 124 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 124 157
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 124 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 124 157 (accept_3_3 11 124 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 124 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 124 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 124 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 124 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 124 157 (accept_3_3 8 124 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 124 157 (Polychromatic418967fa.accept_19_7_10_5_1_3090 7 124 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 124 157
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 124 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 124 157 (accept_3_3 5 124 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  124 157 (Polychromatic418967fa.accept_16_4_12_13_1_990 4 124 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 124 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 124 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 124 157 (accept_3_3 2 124 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 124 157 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 124 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 124 157)))))))))))))))))))))))))))))))))) (allB_succ' 35
  123 157 (Eq.refl Bool.true) (allA_succ_of_accept 34 123 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 123 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 123 157
  (Polychromatic418967fa.accept_12_9_3_1_1_303 33 123 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 123 157 (accept_3_3 32 123 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 123 157 (Polychromatic418967fa.accept_13_5_6_1_1_822 31 123 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 123 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 123 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 123 157 (accept_3_3 29 123 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 123 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 123 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 123 157
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 123 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 123 157 (accept_3_3 26 123 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 123 157 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 123 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 123 157 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 123 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 123 157 (accept_3_3 23 123 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 123 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 123 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 123 157
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 123 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 123 157 (accept_3_3 20 123 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 123 157 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 123 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 123 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 123 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 123 157 (accept_3_3 17 123 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 123 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 123 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 123 157
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 123 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 123 157 (accept_3_3 14 123 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 123 157 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 123 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 123 157 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 123 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 123 157 (accept_3_3 11 123 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 123 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 123 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 123 157
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 123 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 123 157 (accept_3_3 8 123 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  123 157 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 123 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 123 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 123 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 123 157 (accept_3_3 5 123 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 123 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 123 157
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 123 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 123 157 (accept_3_3 2 123 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  123 157 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 123 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 123 157))))))))))))))))))))))))))))))))))) (allB_succ' 36 122 157 (Eq.refl Bool.true)
  (allA_of_3_1 36 122 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 121 157 (Eq.refl Bool.true)
  (allA_succ_of_accept 36 121 157 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 121 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 121 157 (accept_3_3 35 121 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 121 157 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 121 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 121 157 (Polychromatic418967fa.accept_7_5_2_3_1_106
  33 121 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 121 157 (accept_3_3 32
  121 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 121 157
  (Polychromatic418967fa.accept_13_5_4_1_1_364 31 121 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 121 157 (Polychromatic418967fa.accept_20_10_1_17_1_8614 30 121 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 121 157 (accept_3_3 29 121 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 121 157 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 121 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 121 157
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 121 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 121 157 (accept_3_3 26 121 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 121 157 (Polychromatic418967fa.accept_15_10_1_7_1_5207 25 121 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 121 157 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 121 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 121 157 (accept_3_3 23 121 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 121 157 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 121 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 121 157
  (Polychromatic418967fa.accept_15_6_1_7_1_4079 21 121 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 121 157 (accept_3_3 20 121 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 121 157 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 121 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 121 157 (Polychromatic418967fa.accept_13_5_4_1_1_364 18 121 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 121 157 (accept_3_3 17 121 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 121 157 (Polychromatic418967fa.accept_10_6_1_7_1_342 16 121
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 121 157
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 121 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 121 157 (accept_3_3 14 121 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 121 157 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 121 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 121 157 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 121 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 121 157 (accept_3_3 11 121 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 121 157 (Polychromatic418967fa.accept_13_10_4_1_1_2142 10 121 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 121 157
  (Polychromatic418967fa.accept_15_9_1_7_1_1350 9 121 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 121 157 (accept_3_3 8 121 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  121 157 (Polychromatic418967fa.accept_16_7_9_13_1_4948 7 121 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 121 157 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 121 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 121 157 (accept_3_3 5 121 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 121 157 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 121 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 121 157
  (Polychromatic418967fa.accept_13_3_4_1_1_363 3 121 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 121 157 (accept_3_3 2 121 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  121 157 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 121 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 121 157))))))))))))))))))))))))))))))))))))) (allB_succ' 38 120 157 (Eq.refl Bool.true)
  (allA_succ_of_accept 37 120 157 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 120 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 120 157 (Polychromatic418967fa.accept_16_4_8_13_1_1059 36 120
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 120 157 (accept_3_3 35 120
  157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 120 157
  (Polychromatic418967fa.accept_9_7_3_4_1_218 34 120 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 120 157 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 120 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 120 157 (accept_3_3 32 120 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 120 157 (Polychromatic418967fa.accept_13_5_3_1_1_1398 31 120 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 120 157
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 120 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 120 157 (accept_3_3 29 120 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 120 157 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 120 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 120 157 (Polychromatic418967fa.accept_16_11_8_13_1_3844 27 120 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 120 157 (accept_3_3 26 120 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 120 157 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 120 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 120 157
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 120 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 120 157 (accept_3_3 23 120 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 120 157 (Polychromatic418967fa.accept_17_5_1_4_1_3460 22 120 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 120 157 (Polychromatic418967fa.accept_16_5_8_13_1_2764 21 120 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 120 157 (accept_3_3 20 120 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 120 157 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 120 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 120 157
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 120 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 120 157 (accept_3_3 17 120 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 120 157 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 120 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 120 157 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 120 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 120 157 (accept_3_3 14 120 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 120 157 (Polychromatic418967fa.accept_22_13_10_3_1_8613 13 120 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 120 157
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 120 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 120 157 (accept_3_3 11 120 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 120 157 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 120 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 120 157 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 120 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 120 157 (accept_3_3 8 120 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 120 157 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 120 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 120 157
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 120 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 120 157 (accept_3_3 5 120 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  120 157 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 120 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 120 157 (Polychromatic418967fa.accept_16_3_8_13_1_3867 3 120 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 120 157 (accept_3_3 2 120 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 120 157 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 120 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120 157))))))))))))))))))))))))))))))))))))))
  (allB_succ' 39 119 157 (Eq.refl Bool.true) (allA_of_3_1 39 119 157 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 40 118 157 (Eq.refl Bool.true) (allA_succ_of_accept 39 118 157 (Polychromatic418967fa.accept_4_3_2_1_1_50
  39 118 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 118 157 (accept_3_3 38
  118 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 118 157
  (Polychromatic418967fa.accept_7_2_6_3_1_100 37 118 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 118 157 (Polychromatic418967fa.accept_15_6_13_7_1_222 36 118 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 118 157 (accept_3_3 35 118 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 118 157 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 118 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 118 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 33
  118 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 118 157 (accept_3_3 32
  118 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 118 157
  (Polychromatic418967fa.accept_4_3_2_1_1_50 31 118 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 118 157 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 118 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 118 157 (accept_3_3 29 118 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 118 157 (Polychromatic418967fa.accept_11_6_8_3_1_2236 28 118 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 118 157
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 118 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 118 157 (accept_3_3 26 118 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 118 157 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 118 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 118 157 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 118 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 118 157 (accept_3_3 23 118 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 118 157 (Polychromatic418967fa.accept_17_5_16_4_1_4734 22 118 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 118 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 118 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 118 157 (accept_3_3 20 118 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 118 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 118 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 118 157 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 118 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 118 157 (accept_3_3 17 118 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 118 157 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 118 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 118 157
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 118 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 118 157 (accept_3_3 14 118 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 118 157 (Polychromatic418967fa.accept_22_13_8_3_1_8612 13 118 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 118 157 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 118 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 118 157 (accept_3_3 11 118 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 118 157 (Polychromatic418967fa.accept_14_10_6_3_1_1055 10 118 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 118 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 118 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 118 157 (accept_3_3 8 118 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  118 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 118 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 118 157 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 118 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 118 157 (accept_3_3 5 118 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 118 157 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 118 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 118 157
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 118 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 118 157 (accept_3_3 2 118 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  118 157 (Polychromatic418967fa.accept_18_1_10_13_1_500 1 118 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 118 157)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 117 157 (Eq.refl Bool.true)
  (allA_succ_of_accept 40 117 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 117 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 117 157 (Polychromatic418967fa.accept_12_3_9_1_1_290 39 117
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 117 157 (accept_3_3 38 117
  157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 157
  (Polychromatic418967fa.accept_7_2_5_3_1_98 37 117 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 117 157 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 117 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 117 157 (accept_3_3 35 117 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 117 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 117 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 117 157
  (Polychromatic418967fa.accept_15_3_12_7_1_1346 33 117 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 117 157 (accept_3_3 32 117 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 117 157 (Polychromatic418967fa.accept_23_8_2_19_1_6832 31 117 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 117 157 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 117 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 117 157 (accept_3_3 29 117 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 117 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 117 157
  (Polychromatic418967fa.accept_12_3_9_1_1_290 27 117 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 117 157 (accept_3_3 26 117 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 117 157 (Polychromatic418967fa.accept_15_10_12_7_1_1358 25 117 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 117 157 (Polychromatic418967fa.accept_16_8_5_13_1_1021 24 117 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 117 157 (accept_3_3 23 117 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 117 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 117 157
  (Polychromatic418967fa.accept_11_10_7_3_1_3679 21 117 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 117 157 (accept_3_3 20 117 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 117 157 (Polychromatic418967fa.accept_15_4_12_7_1_3115 19 117 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 117 157 (Polychromatic418967fa.accept_15_3_12_7_1_1346 18 117 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 117 157 (accept_3_3 17 117 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 117 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 117 157
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 117 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 117 157 (accept_3_3 14 117 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 117 157 (Polychromatic418967fa.accept_23_13_2_19_1_8611 13 117 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 117 157 (Polychromatic418967fa.accept_14_12_5_3_1_1011 12 117 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 117 157 (accept_3_3 11 117 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 117 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 157
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 117 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 117 157 (accept_3_3 8 117 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  117 157 (Polychromatic418967fa.accept_19_7_3_5_1_8585 7 117 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 117 157 (Polychromatic418967fa.accept_15_6_12_7_1_1360 6 117 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 117 157 (accept_3_3 5 117 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 117 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 117 157
  (Polychromatic418967fa.accept_12_3_9_1_1_290 3 117 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 117 157 (accept_3_3 2 117 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  117 157 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 117 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 117 157))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 116 157 (Eq.refl Bool.true)
  (allA_of_3_1 42 116 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 115 157 (Eq.refl Bool.true)
  (allA_succ_of_accept 42 115 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 115 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 115 157 (accept_3_3 41 115 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 115 157 (Polychromatic418967fa.accept_16_8_3_13_1_7295 40 115 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 115 157
  (Polychromatic418967fa.accept_9_3_7_4_1_53 39 115 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 115 157 (accept_3_3 38 115 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 115 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 115 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 115 157 (Polychromatic418967fa.accept_13_10_11_1_1_2152 36 115 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 115 157 (accept_3_3 35 115 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 115 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 115 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 115 157
  (Polychromatic418967fa.accept_9_6_7_4_1_212 33 115 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 115 157 (accept_3_3 32 115 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 115 157 (Polychromatic418967fa.accept_15_1_10_7_1_4087 31 115 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 115 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 115 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 115 157 (accept_3_3 29 115 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 115 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 115 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 115 157
  (Polychromatic418967fa.accept_15_12_10_7_1_1357 27 115 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 115 157 (accept_3_3 26 115 157 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 115 157 (Polychromatic418967fa.accept_13_12_11_1_1_2920 25 115 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 115 157 (Polychromatic418967fa.accept_9_6_7_4_1_212
  24 115 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 115 157 (accept_3_3 23
  115 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 115 157
  (Polychromatic418967fa.accept_4_2_3_1_1_2 22 115 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 115 157 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 115 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 115 157 (accept_3_3 20 115 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 115 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 115 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 115 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 18
  115 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 115 157 (accept_3_3 17
  115 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 115 157
  (Polychromatic418967fa.accept_13_3_11_1_1_2122 16 115 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 115 157 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 115 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 115 157 (accept_3_3 14 115 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 115 157 (Polychromatic418967fa.accept_10_3_5_7_1_330 13 115 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 115 157
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 115 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 115 157 (accept_3_3 11 115 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 115 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 115 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 115 157 (Polychromatic418967fa.accept_13_9_11_1_1_1375 9 115 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 115 157 (accept_3_3 8 115 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 115 157 (Polychromatic418967fa.accept_13_7_11_1_1_2903 7 115
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 115 157
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 115 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 115 157 (accept_3_3 5 115 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  115 157 (Polychromatic418967fa.accept_15_4_10_7_1_1356 4 115 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 115 157 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 115 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 157 (accept_3_3 2 115 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 115 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 115 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115 157)))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 44 114 157 (Eq.refl Bool.true) (allA_succ_of_accept 43 114 157 (Polychromatic418967fa.accept_4_3_2_1_1_50
  43 114 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 114 157
  (Polychromatic418967fa.accept_10_2_4_7_1_352 42 114 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 114 157 (accept_3_3 41 114 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 114 157 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 114 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 114 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 114 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 114 157 (accept_3_3 38 114 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 114 157 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 114 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 114 157
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 114 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 114 157 (accept_3_3 35 114 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 114 157 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 114 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 114 157 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 114 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 114 157 (accept_3_3 32 114 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 114 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 114 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 114 157
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 114 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 114 157 (accept_3_3 29 114 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 114 157 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 114 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 114 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 114 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 114 157 (accept_3_3 26 114 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 114 157 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 114 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 114 157
  (Polychromatic418967fa.accept_13_11_10_1_1_1409 24 114 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 114 157 (accept_3_3 23 114 157 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 114 157 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 114 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 114 157 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 114 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 114 157 (accept_3_3 20 114 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 114 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 19
  114 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 114 157
  (Polychromatic418967fa.accept_11_7_4_3_1_302 18 114 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 114 157 (accept_3_3 17 114 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 114 157 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 114 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 114 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 114 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 114 157 (accept_3_3 14 114 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 114 157 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 114 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 114 157
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 114 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 114 157 (accept_3_3 11 114 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 114 157 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 114 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 114 157 (Polychromatic418967fa.accept_13_9_10_1_1_1389 9 114 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 114 157 (accept_3_3 8 114 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 114 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 114 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 114 157
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 114 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 114 157 (accept_3_3 5 114 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  114 157 (Polychromatic418967fa.accept_13_4_10_1_1_1390 4 114 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 114 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 114 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 114 157 (accept_3_3 2 114 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 114 157 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 114 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114 157))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 45 113 157 (Eq.refl Bool.true) (allA_of_3_1 45 113 157 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 46 112 157 (Eq.refl Bool.true) (allA_succ_of_accept 45 112 157 (Polychromatic418967fa.accept_6_3_4_1_1_8
  45 112 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 112 157 (accept_3_3 44
  112 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 112 157
  (Polychromatic418967fa.accept_18_7_4_13_1_3315 43 112 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 112 157 (Polychromatic418967fa.accept_20_2_12_17_1_5547 42 112 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 112 157 (accept_3_3 41 112 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 112 157 (Polychromatic418967fa.accept_17_6_10_4_1_6007 40 112 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 112 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 112 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 112 157 (accept_3_3 38 112 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 112 157 (Polychromatic418967fa.accept_13_11_8_1_1_3815 37 112 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 112 157 (Polychromatic418967fa.accept_21_15_7_10_1_8610 36 112 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 112 157 (accept_3_3 35 112 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 112 157 (Polychromatic418967fa.accept_10_4_2_7_1_373 34 112
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 112 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 112 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 112 157 (accept_3_3 32 112 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 112 157 (Polychromatic418967fa.accept_13_5_8_1_1_2161 31 112 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 112 157 (Polychromatic418967fa.accept_19_11_17_5_1_8609 30 112 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 112 157 (accept_3_3 29 112 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 112 157 (Polychromatic418967fa.accept_17_11_10_4_1_5955 28 112
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 112 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 112 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 112 157 (accept_3_3 26 112 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 112 157 (Polychromatic418967fa.accept_10_5_2_7_1_345 25 112 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 112 157 (Polychromatic418967fa.accept_10_4_2_7_1_373 24 112 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 112 157 (accept_3_3 23 112 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 112 157 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 112
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 112 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 112 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 112 157 (accept_3_3 20 112 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 112 157 (Polychromatic418967fa.accept_10_9_2_7_1_1096 19 112 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 112 157 (Polychromatic418967fa.accept_13_5_8_1_1_2161 18 112 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 112 157 (accept_3_3 17 112 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 112 157 (Polychromatic418967fa.accept_21_16_7_10_1_8601 16 112
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 112 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 112 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 112 157 (accept_3_3 14 112 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 112 157 (Polychromatic418967fa.accept_21_13_7_10_1_8599 13 112 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 112 157 (Polychromatic418967fa.accept_11_1_2_3_1_688 12 112 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 112 157 (accept_3_3 11 112 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 112 157 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 112
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 112 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 112 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 112 157 (accept_3_3 8 112 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  112 157 (Polychromatic418967fa.accept_13_7_8_1_1_2145 7 112 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 112 157 (Polychromatic418967fa.accept_13_6_8_1_1_2913 6 112 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 112 157 (accept_3_3 5 112 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 112 157 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 112 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 112 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 112 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 112 157 (accept_3_3 2 112 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  112 157 (Polychromatic418967fa.accept_11_1_2_3_1_688 1 112 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 112 157)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 111 157 (Eq.refl Bool.true)
  (allA_succ_of_accept 46 111 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 111 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 111 157 (Polychromatic418967fa.accept_12_9_3_1_1_303 45 111
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 111 157 (accept_3_3 44 111
  157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 157
  (Polychromatic418967fa.accept_9_7_3_4_1_218 43 111 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 111 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 111 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 111 157 (accept_3_3 41 111 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 111 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 111 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 111 157 (Polychromatic418967fa.accept_7_4_6_3_1_271
  39 111 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 111 157 (accept_3_3 38
  111 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 157
  (Polychromatic418967fa.accept_7_2_6_3_1_100 37 111 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 111 157 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 111 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 111 157 (accept_3_3 35 111 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 111 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 111 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 111 157 (Polychromatic418967fa.accept_9_6_3_4_1_477
  33 111 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 111 157 (accept_3_3 32
  111 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 157
  (Polychromatic418967fa.accept_15_1_6_7_1_6282 31 111 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 111 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 111 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 111 157 (accept_3_3 29 111 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 111 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 111 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 111 157
  (Polychromatic418967fa.accept_15_12_6_7_1_1353 27 111 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 111 157 (accept_3_3 26 111 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 111 157 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 111 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 111 157 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 111 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 111 157 (accept_3_3 23 111 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 111 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 111 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 111 157
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 111 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 111 157 (accept_3_3 20 111 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 111 157 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 111 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 111 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 111 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 157 (accept_3_3 17 111 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 111 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 111 157
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 111 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 111 157 (accept_3_3 14 111 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 111 157 (Polychromatic418967fa.accept_11_2_1_3_1_683 13 111 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 111 157 (Polychromatic418967fa.accept_15_12_6_7_1_1353 12 111 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 157 (accept_3_3 11 111 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 111 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 111 157
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 111 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 111 157 (accept_3_3 8 111 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  111 157 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 111 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 111 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 111 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 157 (accept_3_3 5 111 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 111 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 111 157
  (Polychromatic418967fa.accept_13_3_7_1_1_334 3 111 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 111 157 (accept_3_3 2 111 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  111 157 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 111 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 111 157))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 110 157 (Eq.refl
  Bool.true) (allA_of_3_1 48 110 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 109 157 (Eq.refl Bool.true)
  (allA_succ_of_accept 48 109 157 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 109 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 109 157 (accept_3_3 47 109 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 109 157 (Polychromatic418967fa.accept_17_12_7_4_1_7231 46 109 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 109 157
  (Polychromatic418967fa.accept_13_6_5_1_1_834 45 109 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 109 157 (accept_3_3 44 109 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 109 157 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 109 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 109 157 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 109 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 109 157 (accept_3_3 41 109 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 109 157 (Polychromatic418967fa.accept_11_7_10_3_1_633 40 109 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 109 157
  (Polychromatic418967fa.accept_9_3_1_4_1_216 39 109 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 109 157 (accept_3_3 38 109 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 109 157 (Polychromatic418967fa.accept_17_3_7_4_1_7230 37 109 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 109 157 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 109 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 109 157 (accept_3_3 35 109 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 109 157 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 109 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 109 157
  (Polychromatic418967fa.accept_9_6_1_4_1_474 33 109 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 109 157 (accept_3_3 32 109 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 109 157 (Polychromatic418967fa.accept_17_14_7_4_1_3476 31 109 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 109 157 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 109 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 109 157 (accept_3_3 29 109 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 109 157 (Polychromatic418967fa.accept_10_8_9_7_1_1118 28 109 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 109 157
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 109 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 109 157 (accept_3_3 26 109 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 109 157 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 109 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 109 157 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 109 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 109 157 (accept_3_3 23 109 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 109 157 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 109 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 109 157
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 109 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 109 157 (accept_3_3 20 109 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 109 157 (Polychromatic418967fa.accept_13_6_5_1_1_834 19 109 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 109 157 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 109 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 109 157 (accept_3_3 17 109 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 109 157 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 109 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 109 157
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 109 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 109 157 (accept_3_3 14 109 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 109 157 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 109 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 109 157 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 109 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 109 157 (accept_3_3 11 109 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 109 157 (Polychromatic418967fa.accept_15_10_4_7_1_3127 10 109 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 109 157
  (Polychromatic418967fa.accept_13_9_5_1_1_1382 9 109 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 109 157 (accept_3_3 8 109 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  109 157 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 109 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 109 157 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 109 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 109 157 (accept_3_3 5 109 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 109 157 (Polychromatic418967fa.accept_13_4_5_1_1_833 4 109 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 109 157
  (Polychromatic418967fa.accept_9_3_1_4_1_216 3 109 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 109 157 (accept_3_3 2 109 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  109 157 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 109 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 109 157))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 108 157 (Eq.refl
  Bool.true) (allA_succ_of_accept 49 108 157 (Polychromatic418967fa.accept_8_1_4_5_1_48 49 108 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 108 157
  (Polychromatic418967fa.accept_14_6_10_3_1_1038 48 108 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 108 157 (accept_3_3 47 108 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 108 157 (Polychromatic418967fa.accept_19_8_13_5_1_1889 46 108 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 108 157 (Polychromatic418967fa.accept_10_5_8_7_1_2174 45 108 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 108 157 (accept_3_3 44 108 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 108 157 (Polychromatic418967fa.accept_21_1_3_10_1_5401 43 108
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 108 157
  (Polychromatic418967fa.accept_13_3_4_1_1_363 42 108 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 108 157 (accept_3_3 41 108 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 108 157 (Polychromatic418967fa.accept_15_10_3_7_1_715 40 108 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 108 157 (Polychromatic418967fa.accept_10_9_8_7_1_714 39 108 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 108 157 (accept_3_3 38 108 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 108 157 (Polychromatic418967fa.accept_19_18_13_5_1_8608 37 108
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 108 157
  (Polychromatic418967fa.accept_13_10_4_1_1_2142 36 108 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 108 157 (accept_3_3 35 108 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 108 157 (Polychromatic418967fa.accept_14_6_10_3_1_1038 34 108 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 108 157 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 108 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 108 157 (accept_3_3 32 108 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 108 157 (Polychromatic418967fa.accept_13_5_4_1_1_364 31 108 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 108 157
  (Polychromatic418967fa.accept_19_11_13_5_1_5714 30 108 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 108 157 (accept_3_3 29 108 157 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 108 157 (Polychromatic418967fa.accept_11_6_9_3_1_1103 28 108 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 108 157 (Polychromatic418967fa.accept_14_13_10_3_1_1037 27 108
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 108 157 (accept_3_3 26 108
  157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 108 157
  (Polychromatic418967fa.accept_8_1_4_5_1_48 25 108 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 108 157 (Polychromatic418967fa.accept_16_8_12_13_1_3851 24 108 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 108 157 (accept_3_3 23 108 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 108 157 (Polychromatic418967fa.accept_17_5_6_4_1_8607 22 108 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 108 157
  (Polychromatic418967fa.accept_14_7_10_3_1_1034 21 108 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 108 157 (accept_3_3 20 108 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 108 157 (Polychromatic418967fa.accept_10_9_8_7_1_714 19 108 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 108 157 (Polychromatic418967fa.accept_13_5_4_1_1_364 18 108 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 108 157 (accept_3_3 17 108 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 108 157 (Polychromatic418967fa.accept_13_3_4_1_1_363 16 108
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 108 157
  (Polychromatic418967fa.accept_10_5_8_7_1_2174 15 108 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 108 157 (accept_3_3 14 108 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 108 157 (Polychromatic418967fa.accept_14_13_10_3_1_1037 13 108 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 108 157 (Polychromatic418967fa.accept_15_12_3_7_1_4123 12 108 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 108 157 (accept_3_3 11 108 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 108 157 (Polychromatic418967fa.accept_13_10_4_1_1_2142 10 108
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 108 157
  (Polychromatic418967fa.accept_8_1_4_5_1_48 9 108 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 108 157 (accept_3_3 8 108 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  108 157 (Polychromatic418967fa.accept_14_7_10_3_1_1034 7 108 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 108 157 (Polychromatic418967fa.accept_11_6_9_3_1_1103 6 108 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 108 157 (accept_3_3 5 108 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 108 157 (Polychromatic418967fa.accept_15_4_3_7_1_713 4 108 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 108 157
  (Polychromatic418967fa.accept_13_3_4_1_1_363 3 108 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 108 157 (accept_3_3 2 108 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  108 157 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 108 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 108 157)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 107 157 (Eq.refl
  Bool.true) (allA_of_3_1 51 107 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 52 106 157 (Eq.refl Bool.true)
  (allA_succ_of_accept 51 106 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 106 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 106 157 (accept_3_3 50 106 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 106 157 (Polychromatic418967fa.accept_20_9_6_17_1_1654 49 106 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 106 157
  (Polychromatic418967fa.accept_9_3_7_4_1_53 48 106 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 106 157 (accept_3_3 47 106 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 106 157 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 106 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 106 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 106 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 106 157 (accept_3_3 44 106 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 106 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 106 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 106 157
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 106 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 106 157 (accept_3_3 41 106 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 106 157 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 106 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 106 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 106 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 106 157 (accept_3_3 38 106 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 106 157 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 106 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 106 157
  (Polychromatic418967fa.accept_15_6_1_7_1_4079 36 106 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 106 157 (accept_3_3 35 106 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 106 157 (Polychromatic418967fa.accept_19_15_11_5_1_5713 34 106 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 106 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 106 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 106 157 (accept_3_3 32 106 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 106 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 106 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 106 157
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 106 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 106 157 (accept_3_3 29 106 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 106 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 106 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 106 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 106 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 106 157 (accept_3_3 26 106 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 106 157 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 106 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 106 157
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 106 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 106 157 (accept_3_3 23 106 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 106 157 (Polychromatic418967fa.accept_13_9_2_1_1_813 22 106 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 106 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 106 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 106 157 (accept_3_3 20 106 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 106 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 106 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 106 157
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 106 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 106 157 (accept_3_3 17 106 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 106 157 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 106 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 106 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 106 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 106 157 (accept_3_3 14 106 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 106 157 (Polychromatic418967fa.accept_10_3_6_7_1_2188 13 106 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 106 157
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 106 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 106 157 (accept_3_3 11 106 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 106 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 106 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 106 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 106 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 106 157 (accept_3_3 8 106 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 106 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 106 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 106 157
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 106 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 106 157 (accept_3_3 5 106 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  106 157 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 106 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 106 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 106 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 106 157 (accept_3_3 2 106 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 106 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 106 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106
  157)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 105 157 (Eq.refl Bool.true)
  (allA_succ_of_accept 52 105 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 105 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 105 157 (Polychromatic418967fa.accept_12_3_9_1_1_290 51 105
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 105 157 (accept_3_3 50 105
  157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 105 157
  (Polychromatic418967fa.accept_16_1_9_13_1_1822 49 105 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 105 157 (Polychromatic418967fa.accept_9_3_6_4_1_210 48 105 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 105 157 (accept_3_3 47 105 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 105 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 105 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 105 157
  (Polychromatic418967fa.accept_19_7_10_5_1_3090 45 105 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 105 157 (accept_3_3 44 105 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 105 157 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 105 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 105 157 (Polychromatic418967fa.accept_10_2_5_7_1_1124 42 105 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 105 157 (accept_3_3 41 105 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 105 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 105 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 105 157
  (Polychromatic418967fa.accept_9_3_6_4_1_210 39 105 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 105 157 (accept_3_3 38 105 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 105 157 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 105 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 105 157 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 105 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 105 157 (accept_3_3 35 105 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 105 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 105 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 105 157
  (Polychromatic418967fa.accept_10_3_5_7_1_330 33 105 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 105 157 (accept_3_3 32 105 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 105 157 (Polychromatic418967fa.accept_11_9_6_3_1_1668 31 105 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 105 157 (Polychromatic418967fa.accept_9_3_6_4_1_210 30 105 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 105 157 (accept_3_3 29 105 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 105 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 105 157
  (Polychromatic418967fa.accept_12_3_9_1_1_290 27 105 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 105 157 (accept_3_3 26 105 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 105 157 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 105 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 105 157 (Polychromatic418967fa.accept_14_10_7_3_1_1022 24 105 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 105 157 (accept_3_3 23 105 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 105 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 105 157
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 105 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 105 157 (accept_3_3 20 105 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 105 157 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 105 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 105 157 (Polychromatic418967fa.accept_10_8_5_7_1_358 18 105 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 157 (accept_3_3 17 105 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 105 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 105 157
  (Polychromatic418967fa.accept_12_3_9_1_1_290 15 105 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 105 157 (accept_3_3 14 105 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 105 157 (Polychromatic418967fa.accept_10_3_5_7_1_330 13 105 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 105 157 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 105 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 157 (accept_3_3 11 105 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 105 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 105 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 105 157
  (Polychromatic418967fa.accept_11_9_6_3_1_1668 9 105 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 105 157 (accept_3_3 8 105 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  105 157 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 105 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 105 157 (Polychromatic418967fa.accept_16_6_9_13_1_2751 6 105 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 105 157 (accept_3_3 5 105 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 105 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 157
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 105 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 105 157 (accept_3_3 2 105 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  105 157 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 105 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 105 157))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 104 157 (Eq.refl
  Bool.true) (allA_of_3_1 54 104 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 55 103 157 (Eq.refl Bool.true)
  (allA_succ_of_accept 54 103 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 103 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 103 157 (accept_3_3 53 103 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 103 157 (Polychromatic418967fa.accept_16_4_7_13_1_2795 52 103 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 103 157
  (Polychromatic418967fa.accept_7_2_5_3_1_98 51 103 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 103 157 (accept_3_3 50 103 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 103 157 (Polychromatic418967fa.accept_21_7_19_10_1_8567 49 103 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 103 157 (Polychromatic418967fa.accept_17_14_1_4_1_2485 48 103 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 103 157 (accept_3_3 47 103 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 103 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 103 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 103 157
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 103 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 103 157 (accept_3_3 44 103 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 103 157 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 103 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 103 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 103 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 103 157 (accept_3_3 41 103 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 103 157 (Polychromatic418967fa.accept_11_7_4_3_1_302 40 103 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 103 157
  (Polychromatic418967fa.accept_15_9_13_7_1_1361 39 103 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 103 157 (accept_3_3 38 103 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 103 157 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 103 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 103 157 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 103 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 103 157 (accept_3_3 35 103 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 103 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 103 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 103 157
  (Polychromatic418967fa.accept_19_14_8_5_1_8606 33 103 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 103 157 (accept_3_3 32 103 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 103 157 (Polychromatic418967fa.accept_13_5_12_1_1_2123 31 103 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 103 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 103 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 103 157 (accept_3_3 29 103 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 103 157 (Polychromatic418967fa.accept_13_2_12_1_1_343 28 103 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 103 157
  (Polychromatic418967fa.accept_22_5_15_3_1_5261 27 103 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 103 157 (accept_3_3 26 103 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 103 157 (Polychromatic418967fa.accept_10_5_3_7_1_1108 25 103 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 103 157 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 103 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 103 157 (accept_3_3 23 103 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 103 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 103 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 103 157
  (Polychromatic418967fa.accept_13_8_12_1_1_4662 21 103 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 103 157 (accept_3_3 20 103 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 103 157 (Polychromatic418967fa.accept_22_19_15_3_1_8605 19 103 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 103 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 103 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 103 157 (accept_3_3 17 103 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 103 157 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 103 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 103 157
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 103 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 103 157 (accept_3_3 14 103 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 103 157 (Polychromatic418967fa.accept_19_13_8_5_1_8539 13 103 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 103 157 (Polychromatic418967fa.accept_14_12_5_3_1_1011 12 103 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 103 157 (accept_3_3 11 103 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 103 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 103 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 103 157
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 103 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 103 157 (accept_3_3 8 103 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  103 157 (Polychromatic418967fa.accept_11_7_4_3_1_302 7 103 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 103 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 103 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 103 157 (accept_3_3 5 103 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 103 157 (Polychromatic418967fa.accept_10_4_3_7_1_1110 4 103 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 103 157
  (Polychromatic418967fa.accept_19_3_8_5_1_1875 3 103 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 103 157 (accept_3_3 2 103 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  103 157 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 103 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 103 157))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 102 157 (Eq.refl
  Bool.true) (allA_succ_of_accept 55 102 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 102 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 102 157 (Polychromatic418967fa.accept_10_4_2_7_1_373
  54 102 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 102 157 (accept_3_3 53
  102 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 102 157
  (Polychromatic418967fa.accept_9_7_3_4_1_218 52 102 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 102 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 102 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 102 157 (accept_3_3 50 102 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 102 157 (Polychromatic418967fa.accept_10_9_2_7_1_1096 49 102 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 102 157
  (Polychromatic418967fa.accept_7_6_4_3_1_266 48 102 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 102 157 (accept_3_3 47 102 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 102 157 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 102 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 102 157 (Polychromatic418967fa.accept_10_5_2_7_1_345 45 102 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 102 157 (accept_3_3 44 102 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 102 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 102 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 102 157
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 102 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 102 157 (accept_3_3 41 102 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 102 157 (Polychromatic418967fa.accept_15_10_12_7_1_1358 40 102 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 102 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 102 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 102 157 (accept_3_3 38 102 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 102 157 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 102 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 102 157
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 102 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 102 157 (accept_3_3 35 102 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 102 157 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 102 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 102 157 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 102 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 102 157 (accept_3_3 32 102 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 102 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 102 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 102 157
  (Polychromatic418967fa.accept_21_9_18_10_1_5388 30 102 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 102 157 (accept_3_3 29 102 157 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 102 157 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 102 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 102 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 102 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 102 157 (accept_3_3 26 102 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 102 157 (Polychromatic418967fa.accept_9_7_3_4_1_218
  25 102 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 102 157
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 102 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 102 157 (accept_3_3 23 102 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 102 157 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 102 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 102 157 (Polychromatic418967fa.accept_13_8_11_1_1_3789 21 102 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 102 157 (accept_3_3 20 102 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 102 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 102 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 102 157
  (Polychromatic418967fa.accept_15_3_12_7_1_1346 18 102 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 102 157 (accept_3_3 17 102 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 102 157 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 102 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 102 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 102 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 102 157 (accept_3_3 14 102 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 102 157 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 102 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 102 157
  (Polychromatic418967fa.accept_13_12_11_1_1_2920 12 102 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 102 157 (accept_3_3 11 102 157 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 102 157 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 102 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 102 157 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 102 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 102 157 (accept_3_3 8 102 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 102 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 7
  102 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 102 157
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 102 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 102 157 (accept_3_3 5 102 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  102 157 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 102 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 102 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 102 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 102 157 (accept_3_3 2 102 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 102 157 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 102 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  157)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 101 157 (Eq.refl Bool.true) (allA_of_3_1 57
  101 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 58 100 157 (Eq.refl Bool.true) (allA_succ_of_accept 57
  100 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 100 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 100 157 (accept_3_3 56 100 157 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 100 157 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 100 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 100 157 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 100 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 100 157 (accept_3_3 53 100 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 100 157 (Polychromatic418967fa.accept_9_7_1_4_1_217
  52 100 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 100 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 100 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 100 157 (accept_3_3 50 100 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 100 157 (Polychromatic418967fa.accept_8_1_4_5_1_48 49 100 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 100 157 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 100 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 100 157 (accept_3_3 47 100 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 100 157 (Polychromatic418967fa.accept_11_2_1_3_1_683 46 100 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 100 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 100 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 100 157 (accept_3_3 44 100 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 100 157 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 100 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 100 157 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 100 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 100 157 (accept_3_3 41 100 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 100 157 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 100 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 100 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 100 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 100 157 (accept_3_3 38 100 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 100 157 (Polychromatic418967fa.accept_13_11_9_1_1_1407 37 100 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 100 157 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 100 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 100 157 (accept_3_3 35 100 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 100 157 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 100 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 100 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 100 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 100 157 (accept_3_3 32 100 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 100 157 (Polychromatic418967fa.accept_13_5_9_1_1_1405 31 100 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 100 157 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 100 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 100 157 (accept_3_3 29 100 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 100 157 (Polychromatic418967fa.accept_13_2_9_1_1_67 28 100 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 100 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 100 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 100 157 (accept_3_3 26 100 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 100 157 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 100 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 100 157 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 100 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 100 157 (accept_3_3 23 100 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 100 157 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 100 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 100 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 100 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 100 157 (accept_3_3 20 100 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 100 157 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 100 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 100 157 (Polychromatic418967fa.accept_13_5_9_1_1_1405 18 100 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 100 157 (accept_3_3 17 100 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 100 157 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 100 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 100 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 100 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 100 157 (accept_3_3 14 100 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 100 157 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 100 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 100 157 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 100 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 100 157 (accept_3_3 11 100 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 100 157 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 100 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 100 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 100 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 100 157 (accept_3_3 8 100 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  100 157 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 100 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 100 157 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 100 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 100 157 (accept_3_3 5 100 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 100 157 (Polychromatic418967fa.accept_15_4_10_7_1_1356 4 100 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 100 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 100 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 100 157 (accept_3_3 2 100 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  100 157 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 100 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 100 157)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 99 157 (Eq.refl
  Bool.true) (allA_succ_of_accept 58 99 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 99 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 157 (Polychromatic418967fa.accept_12_9_3_1_1_303
  57 99 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 99 157 (accept_3_3 56
  99 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 99 157
  (Polychromatic418967fa.accept_20_15_19_17_1_722 55 99 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 99 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 99 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 99 157 (accept_3_3 53 99 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 99 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 99 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 157 (Polychromatic418967fa.accept_7_2_1_3_1_102 51
  99 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 99 157 (accept_3_3 50 99
  157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 99 157
  (Polychromatic418967fa.accept_16_1_3_13_1_2785 49 99 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 99 157 (Polychromatic418967fa.accept_10_8_9_7_1_1118 48 99 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 99 157 (accept_3_3 47 99 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 99 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 99 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 157 (Polychromatic418967fa.accept_12_9_3_1_1_303
  45 99 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 99 157 (accept_3_3 44
  99 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 99 157
  (Polychromatic418967fa.accept_15_13_9_7_1_2194 43 99 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 99 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 99 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 99 157 (accept_3_3 41 99 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 99 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 99 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 157 (Polychromatic418967fa.accept_7_4_1_3_1_277 39
  99 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 99 157 (accept_3_3 38 99
  157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 99 157
  (Polychromatic418967fa.accept_7_2_1_3_1_102 37 99 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 99 157 (Polychromatic418967fa.accept_20_16_19_17_1_723 36 99 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 99 157 (accept_3_3 35 99 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 99 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 99 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 157 (Polychromatic418967fa.accept_7_5_1_3_1_103 33
  99 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 99 157 (accept_3_3 32 99
  157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 157
  (Polychromatic418967fa.accept_13_5_8_1_1_2161 31 99 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 99 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 99 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 157 (accept_3_3 29 99 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 99 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 99 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 157 (Polychromatic418967fa.accept_19_8_4_5_1_8569
  27 99 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 99 157 (accept_3_3 26
  99 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 157
  (Polychromatic418967fa.accept_7_4_1_3_1_277 25 99 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 99 157 (Polychromatic418967fa.accept_13_11_8_1_1_3815 24 99 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 99 157 (accept_3_3 23 99 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 99 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 99 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 157 (Polychromatic418967fa.accept_12_9_3_1_1_303
  21 99 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 99 157 (accept_3_3 20
  99 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 99 157
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 99 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 99 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 99 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 157 (accept_3_3 17 99 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 99 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 99 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 157
  (Polychromatic418967fa.accept_16_15_3_13_1_2818 15 99 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 99 157 (accept_3_3 14 99 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  99 157 (Polychromatic418967fa.accept_15_13_9_7_1_2194 13 99 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 99 157 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 99 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 99 157 (accept_3_3 11 99 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 99 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 157
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 99 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 99 157 (accept_3_3 8 99 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99
  157 (Polychromatic418967fa.accept_13_7_8_1_1_2145 7 99 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 99 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 99 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 157 (accept_3_3 5 99 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 99 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99 157
  (Polychromatic418967fa.accept_18_3_9_13_1_1235 3 99 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 99 157 (accept_3_3 2 99 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99
  157 (Polychromatic418967fa.accept_15_1_9_7_1_3130 1 99 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 99 157))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 98 157 (Eq.refl
  Bool.true) (allA_of_3_1 60 98 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 61 97 157 (Eq.refl Bool.true)
  (allA_succ_of_accept 60 97 157 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 97 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 97 157 (accept_3_3 59 97 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 97 157 (Polychromatic418967fa.accept_7_2_6_3_1_100 58 97 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 97 157 (Polychromatic418967fa.accept_9_3_7_4_1_53 57
  97 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 97 157 (accept_3_3 56 97
  157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 97 157 (Polychromatic418967fa.accept_9_1_7_4_1_52
  55 97 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 97 157
  (Polychromatic418967fa.accept_13_2_6_1_1_3807 54 97 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 97 157 (accept_3_3 53 97 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  97 157 (Polychromatic418967fa.accept_8_4_1_5_1_186 52 97 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 97 157 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 97 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 97 157 (accept_3_3 50 97 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 97 157 (Polychromatic418967fa.accept_21_7_13_10_1_8604 49 97 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 97 157
  (Polychromatic418967fa.accept_9_3_7_4_1_53 48 97 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 97 157 (accept_3_3 47 97 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  97 157 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 97 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 97 157 (Polychromatic418967fa.accept_19_7_2_5_1_5680 45 97 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 97 157 (accept_3_3 44 97 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 97 157 (Polychromatic418967fa.accept_17_9_12_4_1_3468 43 97 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 97 157
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 97 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 97 157 (accept_3_3 41 97 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  97 157 (Polychromatic418967fa.accept_18_4_7_13_1_3303 40 97 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 97 157 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 97 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 97 157 (accept_3_3 38 97 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 97 157 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 97 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 97 157
  (Polychromatic418967fa.accept_8_4_1_5_1_186 36 97 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 97 157 (accept_3_3 35 97 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  97 157 (Polychromatic418967fa.accept_13_8_6_1_1_3808 34 97 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 97 157 (Polychromatic418967fa.accept_9_6_7_4_1_212 33 97 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 97 157 (accept_3_3 32 97 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 97 157 (Polychromatic418967fa.accept_13_5_6_1_1_822 31 97 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 97 157
  (Polychromatic418967fa.accept_7_2_6_3_1_100 30 97 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 97 157 (accept_3_3 29 97 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  97 157 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 97 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 97 157 (Polychromatic418967fa.accept_19_8_2_5_1_5678 27 97 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 97 157 (accept_3_3 26 97 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 97 157 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 97 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 97 157
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 97 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 97 157 (accept_3_3 23 97 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  97 157 (Polychromatic418967fa.accept_13_9_6_1_1_2902 22 97 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 97 157 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 97 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 97 157 (accept_3_3 20 97 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 97 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 97 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 97 157
  (Polychromatic418967fa.accept_7_4_6_3_1_271 18 97 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 97 157 (accept_3_3 17 97 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  97 157 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 97 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 97 157 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 97 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 97 157 (accept_3_3 14 97 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 97 157 (Polychromatic418967fa.accept_27_13_16_22_1_8603 13 97 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 97 157
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 97 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 97 157 (accept_3_3 11 97 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  97 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 97 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 97 157 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 97 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 157 (accept_3_3 8 97 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 97 157 (Polychromatic418967fa.accept_13_7_6_1_1_368 7 97 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 157
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 97 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 97 157 (accept_3_3 5 97 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97
  157 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 97 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 97 157 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 97 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 157 (accept_3_3 2 97 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 97 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 97 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97 157)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 62 96 157 (Eq.refl Bool.true) (allA_succ_of_accept 61 96 157 (Polychromatic418967fa.accept_9_7_6_4_1_483
  61 96 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 96 157
  (Polychromatic418967fa.accept_11_5_8_3_1_66 60 96 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 96 157 (accept_3_3 59 96 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  96 157 (Polychromatic418967fa.accept_7_2_5_3_1_98 58 96 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 96 157 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 96 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 96 157 (accept_3_3 56 96 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 96 157 (Polychromatic418967fa.accept_9_1_6_4_1_49 55 96 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 96 157
  (Polychromatic418967fa.accept_19_16_1_5_1_3084 54 96 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 96 157 (accept_3_3 53 96 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  96 157 (Polychromatic418967fa.accept_9_7_6_4_1_483 52 96 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 96 157 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 96 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 96 157 (accept_3_3 50 96 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 96 157 (Polychromatic418967fa.accept_11_5_8_3_1_66 49 96 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 96 157
  (Polychromatic418967fa.accept_9_3_6_4_1_210 48 96 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 96 157 (accept_3_3 47 96 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  96 157 (Polychromatic418967fa.accept_9_1_6_4_1_49 46 96 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 96 157 (Polychromatic418967fa.accept_13_6_5_1_1_834 45 96 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 96 157 (accept_3_3 44 96 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 96 157 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 96 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 96 157
  (Polychromatic418967fa.accept_13_3_5_1_1_2144 42 96 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 96 157 (accept_3_3 41 96 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  96 157 (Polychromatic418967fa.accept_17_6_11_4_1_1525 40 96 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 96 157 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 96 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 96 157 (accept_3_3 38 96 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 96 157 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 96 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 96 157
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 96 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 96 157 (accept_3_3 35 96 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  96 157 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 96 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 96 157 (Polychromatic418967fa.accept_10_3_6_7_1_2188 33 96 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 96 157 (accept_3_3 32 96 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 96 157 (Polychromatic418967fa.accept_10_1_6_7_1_710 31 96 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 96 157
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 96 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 96 157 (accept_3_3 29 96 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  96 157 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 96 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 96 157 (Polychromatic418967fa.accept_11_5_8_3_1_66 27 96 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 96 157 (accept_3_3 26 96 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 96 157 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 96 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 96 157
  (Polychromatic418967fa.accept_21_3_12_10_1_3885 24 96 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 96 157 (accept_3_3 23 96 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  96 157 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 96 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 96 157 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 96 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 96 157 (accept_3_3 20 96 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 157 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 96 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 96 157
  (Polychromatic418967fa.accept_19_18_1_5_1_5720 18 96 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 96 157 (accept_3_3 17 96 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  96 157 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 96 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 96 157 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 96 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 96 157 (accept_3_3 14 96 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 157 (Polychromatic418967fa.accept_10_3_6_7_1_2188 13 96 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 96 157
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 96 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 96 157 (accept_3_3 11 96 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  96 157 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 96 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 96 157 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 96 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 96 157 (accept_3_3 8 96 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 157 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 96 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 96 157
  (Polychromatic418967fa.accept_11_6_8_3_1_2236 6 96 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 96 157 (accept_3_3 5 96 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 96
  157 (Polychromatic418967fa.accept_13_4_5_1_1_833 4 96 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 96 157 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 96 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 96 157 (accept_3_3 2 96 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 96 157 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 96 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  157)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 95 157 (Eq.refl Bool.true)
  (allA_of_3_1 63 95 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 64 94 157 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 94 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 94 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 94 157 (accept_3_3 62 94 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 94 157 (Polychromatic418967fa.accept_10_1_4_7_1_374 61 94 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 94 157
  (Polychromatic418967fa.accept_27_6_13_22_1_8602 60 94 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 94 157 (accept_3_3 59 94 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  94 157 (Polychromatic418967fa.accept_13_6_3_1_1_1413 58 94 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 94 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 94 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 94 157 (accept_3_3 56 94 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 94 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 94 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 94 157
  (Polychromatic418967fa.accept_13_2_3_1_1_3823 54 94 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 94 157 (accept_3_3 53 94 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  94 157 (Polychromatic418967fa.accept_10_2_4_7_1_352 52 94 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 94 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 94 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 94 157 (accept_3_3 50 94 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 94 157 (Polychromatic418967fa.accept_14_7_10_3_1_1034 49 94 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 94 157
  (Polychromatic418967fa.accept_14_6_10_3_1_1038 48 94 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 94 157 (accept_3_3 47 94 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  94 157 (Polychromatic418967fa.accept_13_7_3_1_1_814 46 94 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 94 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 94 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 94 157 (accept_3_3 44 94 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 94 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 94 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 94 157
  (Polychromatic418967fa.accept_10_2_4_7_1_352 42 94 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 94 157 (accept_3_3 41 94 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  94 157 (Polychromatic418967fa.accept_12_4_10_1_1_706 40 94 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 94 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 94 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 94 157 (accept_3_3 38 94 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 94 157 (Polychromatic418967fa.accept_13_11_3_1_1_1397 37 94 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 94 157
  (Polychromatic418967fa.accept_17_2_9_4_1_3463 36 94 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 94 157 (accept_3_3 35 94 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  94 157 (Polychromatic418967fa.accept_14_6_10_3_1_1038 34 94 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 94 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 94 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 94 157 (accept_3_3 32 94 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 94 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 94 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 94 157
  (Polychromatic418967fa.accept_11_8_6_3_1_661 30 94 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 94 157 (accept_3_3 29 94 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  94 157 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 94 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 94 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 94 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 94 157 (accept_3_3 26 94 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 94 157 (Polychromatic418967fa.accept_15_10_4_7_1_3127 25 94 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 94 157
  (Polychromatic418967fa.accept_13_11_3_1_1_1397 24 94 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 94 157 (accept_3_3 23 94 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  94 157 (Polychromatic418967fa.accept_10_2_4_7_1_352 22 94 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 94 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 94 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 94 157 (accept_3_3 20 94 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 94 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 94 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 94 157
  (Polychromatic418967fa.accept_13_5_3_1_1_1398 18 94 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 94 157 (accept_3_3 17 94 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  94 157 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 94 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 94 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 94 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 94 157 (accept_3_3 14 94 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 94 157 (Polychromatic418967fa.accept_10_3_4_7_1_353 13 94 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 94 157
  (Polychromatic418967fa.accept_10_2_4_7_1_352 12 94 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 94 157 (accept_3_3 11 94 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  94 157 (Polychromatic418967fa.accept_15_10_4_7_1_3127 10 94 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 94 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 94 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 94 157 (accept_3_3 8 94 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 94 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 94 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 94 157
  (Polychromatic418967fa.accept_13_6_3_1_1_1413 6 94 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 94 157 (accept_3_3 5 94 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 94
  157 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 94 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 94 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 94 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 94 157 (accept_3_3 2 94 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 94 157 (Polychromatic418967fa.accept_10_1_4_7_1_374 1 94 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94
  157)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 93 157 (Eq.refl Bool.true)
  (allA_succ_of_accept 64 93 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 93 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 157 (Polychromatic418967fa.accept_11_8_5_3_1_694 63 93 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 93 157 (accept_3_3 62 93 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 93 157 (Polychromatic418967fa.accept_7_5_2_3_1_106 61
  93 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 93 157
  (Polychromatic418967fa.accept_9_6_3_4_1_477 60 93 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 93 157 (accept_3_3 59 93 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  93 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 93 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 93 157 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 93 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 93 157 (accept_3_3 56 93 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 93 157 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 93 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 93 157
  (Polychromatic418967fa.accept_7_5_2_3_1_106 54 93 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 93 157 (accept_3_3 53 93 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  93 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 93 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 93 157 (Polychromatic418967fa.accept_9_6_3_4_1_477 51 93 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 93 157 (accept_3_3 50 93 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 93 157 (Polychromatic418967fa.accept_15_4_3_7_1_713 49 93 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 93 157
  (Polychromatic418967fa.accept_7_6_2_3_1_107 48 93 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 93 157 (accept_3_3 47 93 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  93 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 93 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 93 157 (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 93 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 93 157 (accept_3_3 44 93 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 93 157 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 93 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 93 157
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 93 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 93 157 (accept_3_3 41 93 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  93 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 93 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 93 157 (Polychromatic418967fa.accept_12_3_9_1_1_290 39 93 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 93 157 (accept_3_3 38 93 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 93 157 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 93 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 93 157
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 93 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 93 157 (accept_3_3 35 93 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  93 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 93 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 93 157 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 93 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 93 157 (accept_3_3 32 93 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 93 157 (Polychromatic418967fa.accept_19_12_17_5_1_5702 31 93 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 93 157
  (Polychromatic418967fa.accept_11_8_5_3_1_694 30 93 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 93 157 (accept_3_3 29 93 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  93 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 93 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 93 157 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 93 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 157 (accept_3_3 26 93 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 93 157 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 93 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 93 157
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 93 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 93 157 (accept_3_3 23 93 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  93 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 93 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 93 157 (Polychromatic418967fa.accept_19_2_17_5_1_5643 21 93 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 157 (accept_3_3 20 93 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 157 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 93 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 93 157
  (Polychromatic418967fa.accept_17_1_8_4_1_1519 18 93 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 93 157 (accept_3_3 17 93 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  93 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 93 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 93 157 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 93 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 157 (accept_3_3 14 93 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 157 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 93 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 93 157
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 93 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 93 157 (accept_3_3 11 93 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  93 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 93 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 93 157 (Polychromatic418967fa.accept_13_9_2_1_1_813 9 93 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 157 (accept_3_3 8 93 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 157 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 93 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93 157
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 93 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 157 (accept_3_3 5 93 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93
  157 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 93 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 93 157 (Polychromatic418967fa.accept_12_3_9_1_1_290 3 93 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 157 (accept_3_3 2 93 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 93 157 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 93 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  157))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 92 157 (Eq.refl Bool.true)
  (allA_of_3_1 66 92 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 67 91 157 (Eq.refl Bool.true)
  (allA_succ_of_accept 66 91 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 91 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 91 157 (accept_3_3 65 91 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 91 157 (Polychromatic418967fa.accept_10_4_1_7_1_371 64 91 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 91 157 (Polychromatic418967fa.accept_19_6_15_5_1_5697
  63 91 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 91 157 (accept_3_3 62
  91 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 91 157
  (Polychromatic418967fa.accept_9_7_1_4_1_217 61 91 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 91 157 (Polychromatic418967fa.accept_9_6_1_4_1_474 60 91 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 91 157 (accept_3_3 59 91 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 91 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 91 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 91 157 (Polychromatic418967fa.accept_9_3_1_4_1_216 57
  91 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 91 157 (accept_3_3 56 91
  157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 91 157
  (Polychromatic418967fa.accept_15_10_1_7_1_5207 55 91 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 91 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 91 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 91 157 (accept_3_3 53 91 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 91 157 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 91 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 91 157 (Polychromatic418967fa.accept_9_6_1_4_1_474 51
  91 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 91 157 (accept_3_3 50 91
  157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 91 157
  (Polychromatic418967fa.accept_19_11_15_5_1_5699 49 91 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 91 157 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 91 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 91 157 (accept_3_3 47 91 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 91 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 91 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 91 157 (Polychromatic418967fa.accept_17_11_6_4_1_4729
  45 91 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 91 157 (accept_3_3 44
  91 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 91 157
  (Polychromatic418967fa.accept_9_7_1_4_1_217 43 91 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 91 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 91 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 91 157 (accept_3_3 41 91 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 91 157 (Polychromatic418967fa.accept_15_10_1_7_1_5207 40 91 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 91 157
  (Polychromatic418967fa.accept_9_3_1_4_1_216 39 91 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 91 157 (accept_3_3 38 91 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  91 157 (Polychromatic418967fa.accept_21_16_7_10_1_8601 37 91 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 91 157 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 91 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 91 157 (accept_3_3 35 91 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 91 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 91 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 91 157
  (Polychromatic418967fa.accept_9_6_1_4_1_474 33 91 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 91 157 (accept_3_3 32 91 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  91 157 (Polychromatic418967fa.accept_19_12_15_5_1_8600 31 91 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 91 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 91 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 91 157 (accept_3_3 29 91 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 91 157 (Polychromatic418967fa.accept_17_11_6_4_1_4729 28 91 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 91 157
  (Polychromatic418967fa.accept_17_10_6_4_1_2506 27 91 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 91 157 (accept_3_3 26 91 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  91 157 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 91 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 91 157 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 91 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 91 157 (accept_3_3 23 91 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 91 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 91 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 91 157
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 91 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 91 157 (accept_3_3 20 91 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  91 157 (Polychromatic418967fa.accept_17_2_6_4_1_2431 19 91 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 91 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 91 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 91 157 (accept_3_3 17 91 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 91 157 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 91 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 91 157
  (Polychromatic418967fa.accept_9_6_1_4_1_474 15 91 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 91 157 (accept_3_3 14 91 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  91 157 (Polychromatic418967fa.accept_21_13_7_10_1_8599 13 91 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 91 157 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 91 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 91 157 (accept_3_3 11 91 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 91 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 91 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 157
  (Polychromatic418967fa.accept_15_9_1_7_1_1350 9 91 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 91 157 (accept_3_3 8 91 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 91
  157 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 91 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 91 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 91 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 91 157 (accept_3_3 5 91 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 91 157 (Polychromatic418967fa.accept_10_4_1_7_1_371 4 91 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 91 157 (Polychromatic418967fa.accept_9_3_1_4_1_216 3
  91 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 157 (accept_3_3 2 91 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 91 157 (Polychromatic418967fa.accept_19_1_15_5_1_4357
  1 91 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91
  157))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 90 157 (Eq.refl Bool.true)
  (allA_succ_of_accept 67 90 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 90 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 90 157 (Polychromatic418967fa.accept_14_10_6_3_1_1055 66 90
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 90 157 (accept_3_3 65 90 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 90 157 (Polychromatic418967fa.accept_22_20_2_3_1_6916
  64 90 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 90 157
  (Polychromatic418967fa.accept_4_3_2_1_1_50 63 90 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 90 157 (accept_3_3 62 90 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  90 157 (Polychromatic418967fa.accept_20_1_10_17_1_8598 61 90 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 90 157 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 90 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 90 157 (accept_3_3 59 90 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 90 157 (Polychromatic418967fa.accept_7_2_6_3_1_100 58 90 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 90 157
  (Polychromatic418967fa.accept_13_5_12_1_1_2123 57 90 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 90 157 (accept_3_3 56 90 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  90 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 90 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 90 157 (Polychromatic418967fa.accept_13_2_12_1_1_343 54 90 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 90 157 (accept_3_3 53 90 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 90 157 (Polychromatic418967fa.accept_14_10_6_3_1_1055 52 90 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 90 157
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 90 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 90 157 (accept_3_3 50 90 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  90 157 (Polychromatic418967fa.accept_19_11_14_5_1_5629 49 90 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 90 157 (Polychromatic418967fa.accept_19_10_14_5_1_3079 48 90 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 90 157 (accept_3_3 47 90 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 90 157 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 90 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 90 157
  (Polychromatic418967fa.accept_11_1_2_3_1_688 45 90 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 90 157 (accept_3_3 44 90 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  90 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 90 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 90 157 (Polychromatic418967fa.accept_22_20_2_3_1_6916 42 90 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 90 157 (accept_3_3 41 90 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 90 157 (Polychromatic418967fa.accept_17_6_5_4_1_7238 40 90 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 90 157
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 90 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 90 157 (accept_3_3 38 90 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  90 157 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 90 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 90 157 (Polychromatic418967fa.accept_19_17_14_5_1_8561 36 90 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 90 157 (accept_3_3 35 90 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 90 157 (Polychromatic418967fa.accept_11_1_2_3_1_688 34 90 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 90 157
  (Polychromatic418967fa.accept_17_16_5_4_1_2499 33 90 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 90 157 (accept_3_3 32 90 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  90 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 90 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 90 157 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 90 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 90 157 (accept_3_3 29 90 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 90 157 (Polychromatic418967fa.accept_13_2_12_1_1_343 28 90 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 90 157
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 90 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 90 157 (accept_3_3 26 90 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  90 157 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 90 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 90 157 (Polychromatic418967fa.accept_13_11_12_1_1_2154 24 90 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 90 157 (accept_3_3 23 90 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 90 157 (Polychromatic418967fa.accept_19_3_14_5_1_8597 22 90
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 90 157
  (Polychromatic418967fa.accept_13_8_12_1_1_4662 21 90 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 90 157 (accept_3_3 20 90 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  90 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 90 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 90 157 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 90 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 90 157 (accept_3_3 17 90 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 90 157 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 90 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 90 157
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 90 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 90 157 (accept_3_3 14 90 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  90 157 (Polychromatic418967fa.accept_19_13_14_5_1_8545 13 90 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 90 157 (Polychromatic418967fa.accept_11_1_2_3_1_688 12 90 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 90 157 (accept_3_3 11 90 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 90 157 (Polychromatic418967fa.accept_14_10_6_3_1_1055 10 90 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 90 157
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 90 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 90 157 (accept_3_3 8 90 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90
  157 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 90 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 90 157 (Polychromatic418967fa.accept_17_6_5_4_1_7238 6 90 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 90 157 (accept_3_3 5 90 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 90 157 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 90 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 90 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 90
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 90 157 (accept_3_3 2 90 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 90 157 (Polychromatic418967fa.accept_11_1_2_3_1_688 1
  90 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  157)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 89 157 (Eq.refl Bool.true)
  (allA_of_3_1 69 89 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 70 88 157 (Eq.refl Bool.true)
  (allA_succ_of_accept 69 88 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 88 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 88 157 (accept_3_3 68 88 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 88 157 (Polychromatic418967fa.accept_16_3_8_13_1_3867 67 88 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 88 157
  (Polychromatic418967fa.accept_9_3_7_4_1_53 66 88 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 88 157 (accept_3_3 65 88 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  88 157 (Polychromatic418967fa.accept_7_1_4_3_1_21 64 88 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 88 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 88 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 88 157 (accept_3_3 62 88 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 88 157 (Polychromatic418967fa.accept_13_9_10_1_1_1389 61 88 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 88 157
  (Polychromatic418967fa.accept_9_6_7_4_1_212 60 88 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 88 157 (accept_3_3 59 88 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  88 157 (Polychromatic418967fa.accept_12_10_4_1_1_1843 58 88 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 88 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 88 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 88 157 (accept_3_3 56 88 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 88 157 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 88 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 88 157
  (Polychromatic418967fa.accept_15_9_13_7_1_1361 54 88 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 88 157 (accept_3_3 53 88 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  88 157 (Polychromatic418967fa.accept_16_4_8_13_1_1059 52 88 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 88 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 88 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 88 157 (accept_3_3 50 88 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 88 157 (Polychromatic418967fa.accept_10_9_8_7_1_714 49 88 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 88 157
  (Polychromatic418967fa.accept_7_6_4_3_1_266 48 88 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 88 157 (accept_3_3 47 88 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  88 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 88 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 88 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 88 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 88 157 (accept_3_3 44 88 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 88 157 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 88 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 88 157
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 88 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 88 157 (accept_3_3 41 88 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  88 157 (Polychromatic418967fa.accept_21_19_4_10_1_3914 40 88 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 88 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 88 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 88 157 (accept_3_3 38 88 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 88 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 88 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 88 157
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 88 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 88 157 (accept_3_3 35 88 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  88 157 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 88 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 88 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 88 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 88 157 (accept_3_3 32 88 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 88 157 (Polychromatic418967fa.accept_20_11_8_17_1_8596 31 88 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 88 157
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 88 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 88 157 (accept_3_3 29 88 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  88 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 88 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 88 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 88 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 88 157 (accept_3_3 26 88 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 88 157 (Polychromatic418967fa.accept_10_5_8_7_1_2174 25 88 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 88 157
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 88 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 88 157 (accept_3_3 23 88 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  88 157 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 88 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 88 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 88 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 88 157 (accept_3_3 20 88 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 88 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 88 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 88 157
  (Polychromatic418967fa.accept_25_18_13_7_1_8595 18 88 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 88 157 (accept_3_3 17 88 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  88 157 (Polychromatic418967fa.accept_17_16_3_4_1_6010 16 88 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 88 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 88 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 88 157 (accept_3_3 14 88 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 88 157 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 88 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 88 157
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 88 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 88 157 (accept_3_3 11 88 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  88 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 88 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 88 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 88 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 88 157 (accept_3_3 8 88 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 88 157 (Polychromatic418967fa.accept_14_7_4_3_1_488 7 88 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 88 157
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 88 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 88 157 (accept_3_3 5 88 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 88
  157 (Polychromatic418967fa.accept_13_4_10_1_1_1390 4 88 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 88 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 88 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 88 157 (accept_3_3 2 88 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 88 157 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 88 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88
  157)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 87 157 (Eq.refl Bool.true)
  (allA_succ_of_accept 70 87 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 87 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 157 (Polychromatic418967fa.accept_12_9_3_1_1_303 69 87 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 87 157 (accept_3_3 68 87 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 87 157 (Polychromatic418967fa.accept_13_2_9_1_1_67 67
  87 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 87 157
  (Polychromatic418967fa.accept_4_2_3_1_1_2 66 87 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 87 157 (accept_3_3 65 87 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  87 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 87 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 87 157 (Polychromatic418967fa.accept_13_11_9_1_1_1407 63 87 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 87 157 (accept_3_3 62 87 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 87 157 (Polychromatic418967fa.accept_9_7_6_4_1_483 61 87 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 87 157
  (Polychromatic418967fa.accept_13_8_9_1_1_2147 60 87 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 87 157 (accept_3_3 59 87 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  87 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 87 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 87 157 (Polychromatic418967fa.accept_9_3_6_4_1_210 57 87 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 87 157 (accept_3_3 56 87 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 87 157 (Polychromatic418967fa.accept_9_1_6_4_1_49 55 87 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 87 157
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 87 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 87 157 (accept_3_3 53 87 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  87 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 87 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 87 157 (Polychromatic418967fa.accept_11_7_10_3_1_633 51 87 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 87 157 (accept_3_3 50 87 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 157 (Polychromatic418967fa.accept_13_10_9_1_1_5609 49 87 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 87 157
  (Polychromatic418967fa.accept_9_3_6_4_1_210 48 87 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 87 157 (accept_3_3 47 87 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  87 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 87 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 87 157 (Polychromatic418967fa.accept_12_9_3_1_1_303 45 87 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 87 157 (accept_3_3 44 87 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 87 157 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 87 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 87 157
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 87 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 87 157 (accept_3_3 41 87 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  87 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 87 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 87 157 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 87 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 87 157 (accept_3_3 38 87 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 87 157 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 87 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 87 157
  (Polychromatic418967fa.accept_13_10_9_1_1_5609 36 87 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 87 157 (accept_3_3 35 87 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  87 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 87 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 87 157 (Polychromatic418967fa.accept_12_9_3_1_1_303 33 87 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 87 157 (accept_3_3 32 87 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 157 (Polychromatic418967fa.accept_13_5_9_1_1_1405 31 87 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 87 157
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 87 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 87 157 (accept_3_3 29 87 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  87 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 87 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 87 157 (Polychromatic418967fa.accept_23_4_18_19_1_8594 27 87 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 87 157 (accept_3_3 26 87 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 157 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 87 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 87 157
  (Polychromatic418967fa.accept_13_11_9_1_1_1407 24 87 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 87 157 (accept_3_3 23 87 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  87 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 87 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 87 157 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 87 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 87 157 (accept_3_3 20 87 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 157 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 87 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 87 157
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 87 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 87 157 (accept_3_3 17 87 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  87 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 87 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 87 157 (Polychromatic418967fa.accept_13_2_9_1_1_67 15 87 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 157 (accept_3_3 14 87 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 157 (Polychromatic418967fa.accept_19_13_11_5_1_5692 13 87 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 87 157
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 87 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 87 157 (accept_3_3 11 87 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  87 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 87 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 87 157 (Polychromatic418967fa.accept_12_9_3_1_1_303 9 87 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 157 (accept_3_3 8 87 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 157 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 87 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87 157
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 87 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 87 157 (accept_3_3 5 87 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87
  157 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 87 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 87 157 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 87 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 157 (accept_3_3 2 87 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 87 157 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 87 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  157))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 86 157 (Eq.refl Bool.true)
  (allA_of_3_1 72 86 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 73 85 157 (Eq.refl Bool.true)
  (allA_succ_of_accept 72 85 157 (Polychromatic418967fa.accept_7_2_1_3_1_102 72 85 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 85 157 (accept_3_3 71 85 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 85 157 (Polychromatic418967fa.accept_19_13_9_5_1_8541 70 85 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 85 157
  (Polychromatic418967fa.accept_19_12_9_5_1_8593 69 85 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 85 157 (accept_3_3 68 85 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  85 157 (Polychromatic418967fa.accept_7_4_1_3_1_277 67 85 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 85 157 (Polychromatic418967fa.accept_16_2_5_13_1_3842 66 85 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 85 157 (accept_3_3 65 85 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 85 157 (Polychromatic418967fa.accept_15_4_10_7_1_1356 64 85
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 85 157
  (Polychromatic418967fa.accept_10_3_5_7_1_330 63 85 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 85 157 (accept_3_3 62 85 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  85 157 (Polychromatic418967fa.accept_7_5_1_3_1_103 61 85 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 85 157 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 85 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 85 157 (accept_3_3 59 85 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 85 157 (Polychromatic418967fa.accept_7_2_1_3_1_102 58 85 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 85 157
  (Polychromatic418967fa.accept_15_12_10_7_1_1357 57 85 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 85 157 (accept_3_3 56 85 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  85 157 (Polychromatic418967fa.accept_13_3_7_1_1_334 55 85 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 85 157 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 85 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 85 157 (accept_3_3 53 85 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 85 157 (Polychromatic418967fa.accept_10_2_5_7_1_1124 52 85 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 85 157
  (Polychromatic418967fa.accept_7_2_1_3_1_102 51 85 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 85 157 (accept_3_3 50 85 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  85 157 (Polychromatic418967fa.accept_11_5_8_3_1_66 49 85 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 85 157 (Polychromatic418967fa.accept_10_8_5_7_1_358 48 85 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 85 157 (accept_3_3 47 85 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 85 157 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 85 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 85 157
  (Polychromatic418967fa.accept_13_6_7_1_1_335 45 85 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 85 157 (accept_3_3 44 85 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  85 157 (Polychromatic418967fa.accept_10_3_5_7_1_330 43 85 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 85 157 (Polychromatic418967fa.accept_10_2_5_7_1_1124 42 85 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 85 157 (accept_3_3 41 85 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 85 157 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 85 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 85 157
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 85 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 85 157 (accept_3_3 38 85 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  85 157 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 85 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 85 157 (Polychromatic418967fa.accept_21_15_1_10_1_8592 36 85 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 85 157 (accept_3_3 35 85 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 85 157 (Polychromatic418967fa.accept_13_8_7_1_1_1385 34 85 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 85 157
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 85 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 85 157 (accept_3_3 32 85 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  85 157 (Polychromatic418967fa.accept_15_1_10_7_1_4087 31 85 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 85 157 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 85 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 85 157 (accept_3_3 29 85 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 85 157 (Polychromatic418967fa.accept_10_8_5_7_1_358 28 85 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 85 157
  (Polychromatic418967fa.accept_11_5_8_3_1_66 27 85 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 85 157 (accept_3_3 26 85 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  85 157 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 85 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 85 157 (Polychromatic418967fa.accept_13_11_7_1_1_1386 24 85 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 85 157 (accept_3_3 23 85 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 85 157 (Polychromatic418967fa.accept_10_2_5_7_1_1124 22 85 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 85 157
  (Polychromatic418967fa.accept_13_8_7_1_1_1385 21 85 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 85 157 (accept_3_3 20 85 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  85 157 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 85 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 85 157 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 85 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 85 157 (accept_3_3 17 85 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 85 157 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 85 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 85 157
  (Polychromatic418967fa.accept_19_15_9_5_1_5656 15 85 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 85 157 (accept_3_3 14 85 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  85 157 (Polychromatic418967fa.accept_10_3_5_7_1_330 13 85 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 85 157 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 85 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 85 157 (accept_3_3 11 85 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 85 157 (Polychromatic418967fa.accept_16_10_5_13_1_8591 10 85 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 85 157
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 85 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 85 157 (accept_3_3 8 85 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 85
  157 (Polychromatic418967fa.accept_19_7_9_5_1_8590 7 85 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 85 157 (Polychromatic418967fa.accept_11_6_8_3_1_2236 6 85 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 85 157 (accept_3_3 5 85 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 85 157 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 85 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 85 157
  (Polychromatic418967fa.accept_10_3_5_7_1_330 3 85 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 85 157 (accept_3_3 2 85 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 85
  157 (Polychromatic418967fa.accept_15_1_10_7_1_4087 1 85 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 85 157))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74
  84 157 (Eq.refl Bool.true) (allA_succ_of_accept 73 84 157 (Polychromatic418967fa.accept_8_1_4_5_1_48 73 84 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 84 157
  (Polychromatic418967fa.accept_10_2_4_7_1_352 72 84 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 84 157 (accept_3_3 71 84 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  84 157 (Polychromatic418967fa.accept_9_7_3_4_1_218 70 84 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 84 157 (Polychromatic418967fa.accept_9_6_3_4_1_477 69 84 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 84 157 (accept_3_3 68 84 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 84 157 (Polychromatic418967fa.accept_13_2_6_1_1_3807 67 84 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 84 157
  (Polychromatic418967fa.accept_17_15_16_4_1_2418 66 84 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 84 157 (accept_3_3 65 84 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  84 157 (Polychromatic418967fa.accept_9_1_3_4_1_47 64 84 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 84 157 (Polychromatic418967fa.accept_10_3_4_7_1_353 63 84 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 84 157 (accept_3_3 62 84 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 84 157 (Polychromatic418967fa.accept_9_7_3_4_1_218 61 84 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 84 157
  (Polychromatic418967fa.accept_9_6_3_4_1_477 60 84 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 84 157 (accept_3_3 59 84 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  84 157 (Polychromatic418967fa.accept_15_13_9_7_1_2194 58 84 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 84 157 (Polychromatic418967fa.accept_8_1_4_5_1_48 57 84 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 84 157 (accept_3_3 56 84 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 84 157 (Polychromatic418967fa.accept_9_1_3_4_1_47 55 84 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 84 157
  (Polychromatic418967fa.accept_11_10_7_3_1_3679 54 84 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 84 157 (accept_3_3 53 84 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  84 157 (Polychromatic418967fa.accept_9_7_3_4_1_218 52 84 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 84 157 (Polychromatic418967fa.accept_9_6_3_4_1_477 51 84 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 84 157 (accept_3_3 50 84 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 84 157 (Polychromatic418967fa.accept_8_1_4_5_1_48 49 84 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 84 157
  (Polychromatic418967fa.accept_11_4_7_3_1_289 48 84 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 84 157 (accept_3_3 47 84 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  84 157 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 84 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 84 157 (Polychromatic418967fa.accept_23_22_15_19_1_8589 45 84 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 84 157 (accept_3_3 44 84 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 84 157 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 84 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 84 157
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 84 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 84 157 (accept_3_3 41 84 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  84 157 (Polychromatic418967fa.accept_16_8_4_13_1_1014 40 84 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 84 157 (Polychromatic418967fa.accept_16_7_4_13_1_1057 39 84 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 84 157 (accept_3_3 38 84 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 84 157 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 84 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 84 157
  (Polychromatic418967fa.accept_25_11_9_7_1_8588 36 84 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 84 157 (accept_3_3 35 84 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  84 157 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 84 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 84 157 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 84 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 84 157 (accept_3_3 32 84 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 84 157 (Polychromatic418967fa.accept_10_1_4_7_1_374 31 84 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 84 157
  (Polychromatic418967fa.accept_24_6_12_13_1_8587 30 84 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 84 157 (accept_3_3 29 84 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  84 157 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 84 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 84 157 (Polychromatic418967fa.accept_20_7_4_17_1_4132 27 84 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 84 157 (accept_3_3 26 84 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 84 157 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 84 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 84 157
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 84 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 84 157 (accept_3_3 23 84 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  84 157 (Polychromatic418967fa.accept_10_2_4_7_1_352 22 84 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 84 157 (Polychromatic418967fa.accept_10_1_4_7_1_374 21 84 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 84 157 (accept_3_3 20 84 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 157 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 84 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 84 157
  (Polychromatic418967fa.accept_13_5_6_1_1_822 18 84 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 84 157 (accept_3_3 17 84 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  84 157 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 84 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 84 157 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 84 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 84 157 (accept_3_3 14 84 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 157 (Polychromatic418967fa.accept_10_3_4_7_1_353 13 84 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 84 157
  (Polychromatic418967fa.accept_10_2_4_7_1_352 12 84 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 84 157 (accept_3_3 11 84 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  84 157 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 84 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 84 157 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 84 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 84 157 (accept_3_3 8 84 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 157 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 84 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 84 157
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 84 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 84 157 (accept_3_3 5 84 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 84
  157 (Polychromatic418967fa.accept_11_4_7_3_1_289 4 84 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 84 157 (Polychromatic418967fa.accept_10_3_4_7_1_353 3 84 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 84 157 (accept_3_3 2 84 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 84 157 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 84 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  157)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 83 157 (Eq.refl
  Bool.true) (allA_of_3_1 75 83 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 76 82 157 (Eq.refl Bool.true)
  (allA_succ_of_accept 75 82 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 82 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 82 157 (accept_3_3 74 82 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 82 157 (Polychromatic418967fa.accept_18_1_10_13_1_500 73 82 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 82 157
  (Polychromatic418967fa.accept_7_2_5_3_1_98 72 82 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 82 157 (accept_3_3 71 82 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  82 157 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 82 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 82 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 82 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 82 157 (accept_3_3 68 82 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 82 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 82 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 82 157
  (Polychromatic418967fa.accept_9_3_1_4_1_216 66 82 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 82 157 (accept_3_3 65 82 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  82 157 (Polychromatic418967fa.accept_7_1_5_3_1_268 64 82 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 82 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 82 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 82 157 (accept_3_3 62 82 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 82 157 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 82 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 82 157
  (Polychromatic418967fa.accept_9_6_1_4_1_474 60 82 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 82 157 (accept_3_3 59 82 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  82 157 (Polychromatic418967fa.accept_7_2_5_3_1_98 58 82 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 82 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 82 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 82 157 (accept_3_3 56 82 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 82 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 82 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 82 157
  (Polychromatic418967fa.accept_10_4_2_7_1_373 54 82 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 82 157 (accept_3_3 53 82 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  82 157 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 82 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 82 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 82 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 82 157 (accept_3_3 50 82 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 82 157 (Polychromatic418967fa.accept_10_9_2_7_1_1096 49 82 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 82 157
  (Polychromatic418967fa.accept_9_3_1_4_1_216 48 82 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 82 157 (accept_3_3 47 82 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  82 157 (Polychromatic418967fa.accept_21_4_19_10_1_8531 46 82 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 82 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 82 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 82 157 (accept_3_3 44 82 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 82 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 82 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 82 157
  (Polychromatic418967fa.accept_9_6_1_4_1_474 42 82 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 82 157 (accept_3_3 41 82 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  82 157 (Polychromatic418967fa.accept_12_4_10_1_1_706 40 82 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 82 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 82 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 82 157 (accept_3_3 38 82 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 82 157 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 82 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 82 157
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 82 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 82 157 (accept_3_3 35 82 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  82 157 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 82 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 82 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 82 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 82 157 (accept_3_3 32 82 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 82 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 82 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 82 157
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 82 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 82 157 (accept_3_3 29 82 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  82 157 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 82 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 82 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 82 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 82 157 (accept_3_3 26 82 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 82 157 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 82 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 82 157
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 82 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 82 157 (accept_3_3 23 82 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  82 157 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 82 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 82 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 82 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 82 157 (accept_3_3 20 82 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 82 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 82 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 82 157
  (Polychromatic418967fa.accept_13_5_4_1_1_364 18 82 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 82 157 (accept_3_3 17 82 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  82 157 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 82 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 82 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 82 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 82 157 (accept_3_3 14 82 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 82 157 (Polychromatic418967fa.accept_17_13_14_4_1_2468 13 82 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 82 157
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 82 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 82 157 (accept_3_3 11 82 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  82 157 (Polychromatic418967fa.accept_13_10_4_1_1_2142 10 82 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 82 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 82 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 82 157 (accept_3_3 8 82 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 82 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 82 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 82 157
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 82 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 82 157 (accept_3_3 5 82 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 82
  157 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 82 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 82 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 82 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 157 (accept_3_3 2 82 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 82 157 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 82 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  157)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 81 157 (Eq.refl
  Bool.true) (allA_succ_of_accept 76 81 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 81 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 157 (Polychromatic418967fa.accept_12_3_9_1_1_290
  75 81 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 81 157 (accept_3_3 74
  81 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 81 157
  (Polychromatic418967fa.accept_11_7_4_3_1_302 73 81 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 81 157 (Polychromatic418967fa.accept_13_7_3_1_1_814 72 81 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 157 (accept_3_3 71 81 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 81 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 81 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 157 (Polychromatic418967fa.accept_7_6_4_3_1_266 69
  81 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 81 157 (accept_3_3 68 81
  157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 81 157
  (Polychromatic418967fa.accept_13_2_3_1_1_3823 67 81 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 81 157 (Polychromatic418967fa.accept_10_6_1_7_1_342 66 81 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 157 (accept_3_3 65 81 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 81 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 81 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 157 (Polychromatic418967fa.accept_12_3_9_1_1_290
  63 81 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 81 157 (accept_3_3 62
  81 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 157
  (Polychromatic418967fa.accept_15_1_6_7_1_6282 61 81 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 81 157 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 81 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 157 (accept_3_3 59 81 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 81 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 81 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 157 (Polychromatic418967fa.accept_7_1_4_3_1_21 57
  81 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 81 157 (accept_3_3 56 81
  157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 157
  (Polychromatic418967fa.accept_7_6_4_3_1_266 55 81 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 81 157 (Polychromatic418967fa.accept_10_4_1_7_1_371 54 81 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 157 (accept_3_3 53 81 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 81 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 81 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 157 (Polychromatic418967fa.accept_11_7_4_3_1_302
  51 81 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 81 157 (accept_3_3 50
  81 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 81 157
  (Polychromatic418967fa.accept_14_7_11_3_1_5365 49 81 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 81 157 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 81 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 157 (accept_3_3 47 81 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 81 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 81 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 157 (Polychromatic418967fa.accept_13_6_3_1_1_1413
  45 81 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 81 157 (accept_3_3 44
  81 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 157
  (Polychromatic418967fa.accept_7_1_4_3_1_21 43 81 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 81 157 (Polychromatic418967fa.accept_15_12_6_7_1_1353 42 81 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 157 (accept_3_3 41 81 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 81 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 81 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 157 (Polychromatic418967fa.accept_12_3_9_1_1_290
  39 81 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 81 157 (accept_3_3 38
  81 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 157
  (Polychromatic418967fa.accept_13_11_3_1_1_1397 37 81 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 81 157 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 81 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 157 (accept_3_3 35 81 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 81 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 81 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 157 (Polychromatic418967fa.accept_13_7_3_1_1_814
  33 81 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 81 157 (accept_3_3 32
  81 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 157
  (Polychromatic418967fa.accept_13_5_3_1_1_1398 31 81 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 81 157 (Polychromatic418967fa.accept_13_4_3_1_1_2898 30 81 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 157 (accept_3_3 29 81 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 81 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 81 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 157 (Polychromatic418967fa.accept_7_6_4_3_1_266 27
  81 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 81 157 (accept_3_3 26 81
  157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 157
  (Polychromatic418967fa.accept_16_9_1_13_1_1850 25 81 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 81 157 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 81 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 157 (accept_3_3 23 81 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 81 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 81 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 157 (Polychromatic418967fa.accept_14_7_11_3_1_5365
  21 81 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 81 157 (accept_3_3 20
  81 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 157
  (Polychromatic418967fa.accept_13_6_3_1_1_1413 19 81 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 81 157 (Polychromatic418967fa.accept_11_7_4_3_1_302 18 81 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 157 (accept_3_3 17 81 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 81 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 81 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 157 (Polychromatic418967fa.accept_7_1_4_3_1_21 15
  81 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 81 157 (accept_3_3 14 81
  157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 157
  (Polychromatic418967fa.accept_7_6_4_3_1_266 13 81 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 81 157 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 81 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 157 (accept_3_3 11 81 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 81 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 81 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 157 (Polychromatic418967fa.accept_16_9_1_13_1_1850
  9 81 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 81 157 (accept_3_3 8 81
  157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 157
  (Polychromatic418967fa.accept_11_7_4_3_1_302 7 81 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 81 157 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 81 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 157 (accept_3_3 5 81 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 81 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 81 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 157 (Polychromatic418967fa.accept_12_3_9_1_1_290 3
  81 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 157 (accept_3_3 2 81 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 157 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 81
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81
  157))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 78 80 157 (Eq.refl
  Bool.true) (allA_of_3_1 78 80 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 79 157 (allA_succ_of_accept 78
  79 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 79 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 79 157 (accept_3_3 77 79 157 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 79 157 (Polychromatic418967fa.accept_7_6_2_3_1_107 76 79 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 79 157 (Polychromatic418967fa.accept_7_5_2_3_1_106 75 79 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 79 157 (accept_3_3 74 79 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 79 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 73
  79 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 79 157
  (Polychromatic418967fa.accept_10_2_9_7_1_720 72 79 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 79 157 (accept_3_3 71 79 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  79 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 79 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 79 157 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 79 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 79 157 (accept_3_3 68 79 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 79 157 (Polychromatic418967fa.accept_11_1_2_3_1_688 67 79 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 79 157
  (Polychromatic418967fa.accept_4_2_3_1_1_2 66 79 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 79 157 (accept_3_3 65 79 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  79 157 (Polychromatic418967fa.accept_7_1_2_3_1_257 64 79 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 79 157 (Polychromatic418967fa.accept_15_3_4_7_1_1352 63 79 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 79 157 (accept_3_3 62 79 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 79 157 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 79 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 79 157
  (Polychromatic418967fa.accept_9_6_7_4_1_212 60 79 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 79 157 (accept_3_3 59 79 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  79 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 79 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 79 157 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 79 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 79 157 (accept_3_3 56 79 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 79 157 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 79 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 79 157
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 79 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 79 157 (accept_3_3 53 79 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  79 157 (Polychromatic418967fa.accept_10_2_9_7_1_720 52 79 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 79 157 (Polychromatic418967fa.accept_9_6_7_4_1_212 51 79 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 79 157 (accept_3_3 50 79 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 79 157 (Polychromatic418967fa.accept_17_15_11_4_1_7218 49 79 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 79 157
  (Polychromatic418967fa.accept_7_6_2_3_1_107 48 79 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 79 157 (accept_3_3 47 79 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  79 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 79 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 79 157 (Polychromatic418967fa.accept_11_1_2_3_1_688 45 79 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 79 157 (accept_3_3 44 79 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 79 157 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 79 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 79 157
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 79 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 79 157 (accept_3_3 41 79 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  79 157 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 79 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 79 157 (Polychromatic418967fa.accept_9_3_7_4_1_53 39 79 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 79 157 (accept_3_3 38 79 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 79 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 79 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 79 157
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 79 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 79 157 (accept_3_3 35 79 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  79 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 79 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 79 157 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 79 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 79 157 (accept_3_3 32 79 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 79 157 (Polychromatic418967fa.accept_27_4_25_22_1_8586 31 79 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 79 157
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 79 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 79 157 (accept_3_3 29 79 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  79 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 79 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 79 157 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 79 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 157 (accept_3_3 26 79 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 157 (Polychromatic418967fa.accept_15_10_4_7_1_3127 25 79 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 79 157
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 79 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 79 157 (accept_3_3 23 79 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  79 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 79 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 79 157 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 79 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 157 (accept_3_3 20 79 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 157 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 79 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 157
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 79 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 79 157 (accept_3_3 17 79 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  79 157 (Polychromatic418967fa.accept_19_16_3_5_1_5684 16 79 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 79 157 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 79 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 157 (accept_3_3 14 79 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 157 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 79 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 157
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 79 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 157 (accept_3_3 11 79 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  79 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 79 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 79 157 (Polychromatic418967fa.accept_21_9_16_10_1_5371 9 79 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 157 (accept_3_3 8 79 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 157 (Polychromatic418967fa.accept_19_7_3_5_1_8585 7 79 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 157
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 79 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 157 (accept_3_3 5 79 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  157 (Polychromatic418967fa.accept_18_4_7_13_1_3303 4 79 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 79 157 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 79 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 157 (accept_3_3 2 79 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 79 157 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 79 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79
  157))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 78 157
  (allA_succ_of_accept 77 78 157 (accept_3_3 77 78 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  78 157 (Polychromatic418967fa.accept_31_14_16_2_1_8584 76 78 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 78 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 78 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 78 157 (accept_3_3 74 78 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 78 157 (Polychromatic418967fa.accept_9_1_6_4_1_49 73 78 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 78 157
  (Polychromatic418967fa.accept_7_2_1_3_1_102 72 78 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 78 157 (accept_3_3 71 78 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  78 157 (Polychromatic418967fa.accept_9_7_6_4_1_483 70 78 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 78 157 (Polychromatic418967fa.accept_10_9_8_7_1_714 69 78 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 78 157 (accept_3_3 68 78 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 78 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 78 157
  (Polychromatic418967fa.accept_9_3_6_4_1_210 66 78 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 78 157 (accept_3_3 65 78 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  78 157 (Polychromatic418967fa.accept_9_1_6_4_1_49 64 78 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 78 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 78 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 78 157 (accept_3_3 62 78 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 157 (Polychromatic418967fa.accept_7_5_1_3_1_103 61 78 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 78 157
  (Polychromatic418967fa.accept_7_4_1_3_1_277 60 78 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 78 157 (accept_3_3 59 78 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  78 157 (Polychromatic418967fa.accept_7_2_1_3_1_102 58 78 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 78 157 (Polychromatic418967fa.accept_9_3_6_4_1_210 57 78 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 78 157 (accept_3_3 56 78 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 78 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 78 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 78 157
  (Polychromatic418967fa.accept_7_5_1_3_1_103 54 78 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 78 157 (accept_3_3 53 78 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  78 157 (Polychromatic418967fa.accept_9_7_6_4_1_483 52 78 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 78 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 78 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 78 157 (accept_3_3 50 78 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 157 (Polychromatic418967fa.accept_10_9_8_7_1_714 49 78 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 78 157
  (Polychromatic418967fa.accept_9_3_6_4_1_210 48 78 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 78 157 (accept_3_3 47 78 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  78 157 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 78 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 78 157 (Polychromatic418967fa.accept_10_5_8_7_1_2174 45 78 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 78 157 (accept_3_3 44 78 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 78 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 78 157
  (Polychromatic418967fa.accept_15_12_3_7_1_4123 42 78 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 78 157 (accept_3_3 41 78 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  78 157 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 78 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 78 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 78 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 78 157 (accept_3_3 38 78 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 78 157 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 78 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 78 157
  (Polychromatic418967fa.accept_19_17_2_5_1_7085 36 78 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 78 157 (accept_3_3 35 78 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  78 157 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 78 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 78 157 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 78 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 78 157 (accept_3_3 32 78 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 78 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 78 157
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 78 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 78 157 (accept_3_3 29 78 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  78 157 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 78 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 78 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 78 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 78 157 (accept_3_3 26 78 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 157 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 78 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 78 157
  (Polychromatic418967fa.accept_11_2_1_3_1_683 24 78 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 78 157 (accept_3_3 23 78 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  78 157 (Polychromatic418967fa.accept_19_3_2_5_1_5679 22 78 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 78 157 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 78 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 78 157 (accept_3_3 20 78 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 78 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 157
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 78 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 78 157 (accept_3_3 17 78 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  78 157 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 78 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 78 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 78 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 78 157 (accept_3_3 14 78 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 157 (Polychromatic418967fa.accept_11_2_1_3_1_683 13 78 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 78 157
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 78 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 78 157 (accept_3_3 11 78 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  78 157 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 78 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 78 157 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 78 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 78 157 (accept_3_3 8 78 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 78 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 78 157
  (Polychromatic418967fa.accept_17_6_10_4_1_6007 6 78 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 78 157 (accept_3_3 5 78 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78
  157 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 78 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 78 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 78 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 78 157 (accept_3_3 2 78 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 78 157 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 78 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  157)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 157 (allA_of_3_1 77 77
  157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 76 157 (allA_succ_of_accept 75 76 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 76 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 76 157 (accept_3_3 74 76 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  76 157 (Polychromatic418967fa.accept_8_1_4_5_1_48 73 76 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 76 157 (Polychromatic418967fa.accept_7_2_6_3_1_100 72 76 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 76 157 (accept_3_3 71 76 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 76 157 (Polychromatic418967fa.accept_12_10_4_1_1_1843 70 76 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 76 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 76 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 76 157 (accept_3_3 68 76 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  76 157 (Polychromatic418967fa.accept_7_4_6_3_1_271 67 76 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 76 157 (Polychromatic418967fa.accept_14_10_6_3_1_1055 66 76 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 76 157 (accept_3_3 65 76 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 76 157 (Polychromatic418967fa.accept_13_12_11_1_1_2920 64 76
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 76 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 76 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 76 157 (accept_3_3 62 76 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  76 157 (Polychromatic418967fa.accept_10_1_6_7_1_710 61 76 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 76 157 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 76 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 76 157 (accept_3_3 59 76 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 76 157 (Polychromatic418967fa.accept_7_2_6_3_1_100 58 76 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 76 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 76 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 76 157 (accept_3_3 56 76 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  76 157 (Polychromatic418967fa.accept_13_3_11_1_1_2122 55 76 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 76 157 (Polychromatic418967fa.accept_15_9_1_7_1_1350 54 76 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 76 157 (accept_3_3 53 76 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 76 157 (Polychromatic418967fa.accept_14_10_6_3_1_1055 52 76 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 76 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 76 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 76 157 (accept_3_3 50 76 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  76 157 (Polychromatic418967fa.accept_8_1_4_5_1_48 49 76 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 76 157 (Polychromatic418967fa.accept_13_9_11_1_1_1375 48 76 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 76 157 (accept_3_3 47 76 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 76 157 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 76 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 76 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 76 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 76 157 (accept_3_3 44 76 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  76 157 (Polychromatic418967fa.accept_10_3_6_7_1_2188 43 76 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 76 157 (Polychromatic418967fa.accept_13_3_11_1_1_2122 42 76 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 76 157 (accept_3_3 41 76 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 76 157 (Polychromatic418967fa.accept_11_7_10_3_1_633 40 76 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 76 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 76 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 76 157 (accept_3_3 38 76 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  76 157 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 76 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 76 157 (Polychromatic418967fa.accept_13_10_11_1_1_2152 36 76 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 76 157 (accept_3_3 35 76 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 76 157 (Polychromatic418967fa.accept_12_10_4_1_1_1843 34 76
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 76 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 76 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 76 157 (accept_3_3 32 76 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  76 157 (Polychromatic418967fa.accept_10_1_6_7_1_710 31 76 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 76 157 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 76 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 76 157 (accept_3_3 29 76 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 76 157 (Polychromatic418967fa.accept_18_10_4_13_1_3296 28 76 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 76 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 76 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 76 157 (accept_3_3 26 76 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  76 157 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 76 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 76 157 (Polychromatic418967fa.accept_14_10_6_3_1_1055 24 76 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 76 157 (accept_3_3 23 76 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 76 157 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 76
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 76 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 76 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 76 157 (accept_3_3 20 76 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  76 157 (Polychromatic418967fa.accept_20_19_16_17_1_5473 19 76 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 76 157 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 76 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 76 157 (accept_3_3 17 76 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 76 157 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 76 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 76 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 76 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 76 157 (accept_3_3 14 76 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  76 157 (Polychromatic418967fa.accept_10_3_6_7_1_2188 13 76 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 76 157 (Polychromatic418967fa.accept_13_12_11_1_1_2920 12 76 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 76 157 (accept_3_3 11 76 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 76 157 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 76
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 76 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 76 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 76 157 (accept_3_3 8 76 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 76
  157 (Polychromatic418967fa.accept_11_7_10_3_1_633 7 76 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 76 157 (Polychromatic418967fa.accept_15_6_1_7_1_4079 6 76 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 76 157 (accept_3_3 5 76 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 76 157 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 76 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 76 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 76 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 76 157 (accept_3_3 2 76 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 76
  157 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 76 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 76 157)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 157
  (allA_succ_of_accept 74 75 157 (accept_3_3 74 75 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  75 157 (Polychromatic418967fa.accept_9_1_3_4_1_47 73 75 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 75 157 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 75 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 75 157 (accept_3_3 71 75 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 75 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 75 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 157
  (Polychromatic418967fa.accept_9_6_3_4_1_477 69 75 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 75 157 (accept_3_3 68 75 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  75 157 (Polychromatic418967fa.accept_19_10_18_5_1_5673 67 75 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 75 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 75 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 75 157 (accept_3_3 65 75 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 75 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 157
  (Polychromatic418967fa.accept_10_3_5_7_1_330 63 75 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 75 157 (accept_3_3 62 75 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  75 157 (Polychromatic418967fa.accept_9_7_3_4_1_218 61 75 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 75 157 (Polychromatic418967fa.accept_9_6_3_4_1_477 60 75 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 75 157 (accept_3_3 59 75 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 75 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 157
  (Polychromatic418967fa.accept_7_1_5_3_1_268 57 75 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 75 157 (accept_3_3 56 75 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  75 157 (Polychromatic418967fa.accept_9_1_3_4_1_47 55 75 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 75 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 75 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 75 157 (accept_3_3 53 75 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 75 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 157
  (Polychromatic418967fa.accept_7_2_5_3_1_98 51 75 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 75 157 (accept_3_3 50 75 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  75 157 (Polychromatic418967fa.accept_22_5_9_3_1_5251 49 75 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 75 157 (Polychromatic418967fa.accept_10_8_5_7_1_358 48 75 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 75 157 (accept_3_3 47 75 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 75 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 157
  (Polychromatic418967fa.accept_12_9_3_1_1_303 45 75 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 75 157 (accept_3_3 44 75 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  75 157 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 75 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 75 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 75 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 75 157 (accept_3_3 41 75 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 75 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 157
  (Polychromatic418967fa.accept_11_6_9_3_1_1103 39 75 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 75 157 (accept_3_3 38 75 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  75 157 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 75 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 75 157 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 75 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 75 157 (accept_3_3 35 75 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 75 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 157
  (Polychromatic418967fa.accept_9_6_3_4_1_477 33 75 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 75 157 (accept_3_3 32 75 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  75 157 (Polychromatic418967fa.accept_17_14_7_4_1_3476 31 75 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 75 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 75 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 75 157 (accept_3_3 29 75 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 75 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 157
  (Polychromatic418967fa.accept_18_9_3_13_1_5905 27 75 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 75 157 (accept_3_3 26 75 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  75 157 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 75 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 75 157 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 75 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 75 157 (accept_3_3 23 75 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 75 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 157
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 75 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 75 157 (accept_3_3 20 75 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  75 157 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 75 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 75 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 75 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 157 (accept_3_3 17 75 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 75 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 157
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 75 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 75 157 (accept_3_3 14 75 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  75 157 (Polychromatic418967fa.accept_10_3_5_7_1_330 13 75 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 75 157 (Polychromatic418967fa.accept_10_2_5_7_1_1124 12 75 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 157 (accept_3_3 11 75 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 75 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 157
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 75 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 75 157 (accept_3_3 8 75 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75
  157 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 75 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 75 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 75 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 75 157 (accept_3_3 5 75 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 75 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 75 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 75 157 (Polychromatic418967fa.accept_10_3_5_7_1_330 3
  75 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 157 (accept_3_3 2 75 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 157 (Polychromatic418967fa.accept_7_1_5_3_1_268 1
  75 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  157))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 157 (allA_of_3_1 74 74
  157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 73 157 (allA_succ_of_accept 72 73 157
  (Polychromatic418967fa.accept_13_7_8_1_1_2145 72 73 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 73 157 (accept_3_3 71 73 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  73 157 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 73 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 73 157 (Polychromatic418967fa.accept_9_6_1_4_1_474 69 73 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 157 (accept_3_3 68 73 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 157 (Polychromatic418967fa.accept_17_16_5_4_1_2499 67 73 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 157
  (Polychromatic418967fa.accept_9_3_1_4_1_216 66 73 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 73 157 (accept_3_3 65 73 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  73 157 (Polychromatic418967fa.accept_10_4_3_7_1_1110 64 73 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 73 157 (Polychromatic418967fa.accept_13_11_8_1_1_3815 63 73 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 157 (accept_3_3 62 73 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 157 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 73 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 157
  (Polychromatic418967fa.accept_8_4_1_5_1_186 60 73 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 157 (accept_3_3 59 73 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 157 (Polychromatic418967fa.accept_13_6_8_1_1_2913 58 73 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 157 (Polychromatic418967fa.accept_9_3_1_4_1_216 57 73 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 157 (accept_3_3 56 73 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 157 (Polychromatic418967fa.accept_10_5_3_7_1_1108 55 73 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 157
  (Polychromatic418967fa.accept_10_4_3_7_1_1110 54 73 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 157 (accept_3_3 53 73 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 157 (Polychromatic418967fa.accept_8_4_1_5_1_186 52 73 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 157 (Polychromatic418967fa.accept_9_6_1_4_1_474 51 73 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 157 (accept_3_3 50 73 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 157 (Polychromatic418967fa.accept_16_1_9_13_1_1822 49 73 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 157
  (Polychromatic418967fa.accept_9_3_1_4_1_216 48 73 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 157 (accept_3_3 47 73 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 157 (Polychromatic418967fa.accept_10_6_3_7_1_2197 46 73 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 157 (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 73 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 157 (accept_3_3 44 73 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 157 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 73 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 157
  (Polychromatic418967fa.accept_9_6_1_4_1_474 42 73 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 157 (accept_3_3 41 73 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 157 (Polychromatic418967fa.accept_17_6_5_4_1_7238 40 73 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 157 (Polychromatic418967fa.accept_9_3_1_4_1_216 39 73 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 157 (accept_3_3 38 73 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 157 (Polychromatic418967fa.accept_11_4_7_3_1_289 37 73 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 157
  (Polychromatic418967fa.accept_8_4_1_5_1_186 36 73 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 157 (accept_3_3 35 73 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 157 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 73 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 157 (Polychromatic418967fa.accept_9_6_1_4_1_474 33 73 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 157 (accept_3_3 32 73 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 157 (Polychromatic418967fa.accept_13_5_8_1_1_2161 31 73 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 157
  (Polychromatic418967fa.accept_9_3_1_4_1_216 30 73 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 157 (accept_3_3 29 73 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 157 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 73 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 157 (Polychromatic418967fa.accept_19_8_16_5_1_8583 27 73 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 157 (accept_3_3 26 73 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 157 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 73 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 157
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 73 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 157 (accept_3_3 23 73 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 157 (Polychromatic418967fa.accept_13_9_8_1_1_824 22 73 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 157 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 73 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 157 (accept_3_3 20 73 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 157 (Polychromatic418967fa.accept_13_6_8_1_1_2913 19 73 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 157
  (Polychromatic418967fa.accept_13_5_8_1_1_2161 18 73 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 157 (accept_3_3 17 73 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 157 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 73 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 157 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 73 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 157 (accept_3_3 14 73 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 157 (Polychromatic418967fa.accept_25_13_23_7_1_8582 13 73 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 157
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 73 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 157 (accept_3_3 11 73 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 157 (Polychromatic418967fa.accept_11_10_7_3_1_3679 10 73 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 157 (Polychromatic418967fa.accept_13_9_8_1_1_824 9 73 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 157 (accept_3_3 8 73 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 157 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 73 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 157
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 73 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 157 (accept_3_3 5 73 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  157 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 73 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 157 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 73 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 157 (accept_3_3 2 73 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 157 (Polychromatic418967fa.accept_16_1_9_13_1_1822 1 73 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  157))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 157 (allA_succ_of_accept 71
  72 157 (accept_3_3 71 72 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 72 157
  (Polychromatic418967fa.accept_15_10_12_7_1_1358 70 72 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 72 157 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 72 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 72 157 (accept_3_3 68 72 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 72 157 (Polychromatic418967fa.accept_16_3_8_13_1_3867 67 72 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 72 157
  (Polychromatic418967fa.accept_15_6_12_7_1_1360 66 72 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 72 157 (accept_3_3 65 72 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  72 157 (Polychromatic418967fa.accept_7_1_2_3_1_257 64 72 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 72 157 (Polychromatic418967fa.accept_11_8_6_3_1_661 63 72 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 72 157 (accept_3_3 62 72 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 157 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 72 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 72 157
  (Polychromatic418967fa.accept_13_8_7_1_1_1385 60 72 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 72 157 (accept_3_3 59 72 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  72 157 (Polychromatic418967fa.accept_13_6_7_1_1_335 58 72 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 72 157 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 72 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 72 157 (accept_3_3 56 72 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 157 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 72 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 72 157
  (Polychromatic418967fa.accept_7_5_2_3_1_106 54 72 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 72 157 (accept_3_3 53 72 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  72 157 (Polychromatic418967fa.accept_11_8_6_3_1_661 52 72 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 72 157 (Polychromatic418967fa.accept_15_6_12_7_1_1360 51 72 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 72 157 (accept_3_3 50 72 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 72 157 (Polychromatic418967fa.accept_10_9_2_7_1_1096 49 72 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 72 157
  (Polychromatic418967fa.accept_7_6_2_3_1_107 48 72 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 72 157 (accept_3_3 47 72 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  72 157 (Polychromatic418967fa.accept_20_6_12_17_1_8581 46 72 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 72 157 (Polychromatic418967fa.accept_10_5_2_7_1_345 45 72 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 72 157 (accept_3_3 44 72 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 157 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 72 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 72 157
  (Polychromatic418967fa.accept_11_9_6_3_1_1668 42 72 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 72 157 (accept_3_3 41 72 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  72 157 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 72 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 72 157 (Polychromatic418967fa.accept_10_9_2_7_1_1096 39 72 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 72 157 (accept_3_3 38 72 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 157 (Polychromatic418967fa.accept_13_11_7_1_1_1386 37 72 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 72 157
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 72 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 72 157 (accept_3_3 35 72 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  72 157 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 72 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 72 157 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 72 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 72 157 (accept_3_3 32 72 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 72 157 (Polychromatic418967fa.accept_11_9_6_3_1_1668 31 72 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 72 157
  (Polychromatic418967fa.accept_11_8_6_3_1_661 30 72 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 72 157 (accept_3_3 29 72 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  72 157 (Polychromatic418967fa.accept_16_12_8_13_1_6073 28 72 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 72 157 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 72 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 72 157 (accept_3_3 26 72 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 157 (Polychromatic418967fa.accept_10_5_2_7_1_345 25 72 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 72 157
  (Polychromatic418967fa.accept_10_4_2_7_1_373 24 72 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 72 157 (accept_3_3 23 72 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  72 157 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 72 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 72 157 (Polychromatic418967fa.accept_13_8_7_1_1_1385 21 72 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 72 157 (accept_3_3 20 72 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 157 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 72 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 72 157
  (Polychromatic418967fa.accept_15_3_12_7_1_1346 18 72 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 72 157 (accept_3_3 17 72 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  72 157 (Polychromatic418967fa.accept_13_3_7_1_1_334 16 72 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 72 157 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 72 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 72 157 (accept_3_3 14 72 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 157 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 72 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 72 157
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 72 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 72 157 (accept_3_3 11 72 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  72 157 (Polychromatic418967fa.accept_15_10_12_7_1_1358 10 72 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 72 157 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 72 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 72 157 (accept_3_3 8 72 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 157 (Polychromatic418967fa.accept_20_7_12_17_1_8580 7 72 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 72 157
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 72 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 72 157 (accept_3_3 5 72 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 72
  157 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 72 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 72 157 (Polychromatic418967fa.accept_13_3_7_1_1_334 3 72 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 72 157 (accept_3_3 2 72 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 72 157 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 72 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72
  157)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 157 (allA_of_3_1 71 71 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 70 157 (allA_succ_of_accept 69 70 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 70 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 70 157 (accept_3_3 68 70 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  70 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 70 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 70 157 (Polychromatic418967fa.accept_9_3_7_4_1_53 66 70 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 70 157 (accept_3_3 65 70 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 70 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 64 70 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 70 157
  (Polychromatic418967fa.accept_4_3_2_1_1_50 63 70 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 70 157 (accept_3_3 62 70 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  70 157 (Polychromatic418967fa.accept_13_9_5_1_1_1382 61 70 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 70 157 (Polychromatic418967fa.accept_9_6_7_4_1_212 60 70 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 70 157 (accept_3_3 59 70 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 70 157 (Polychromatic418967fa.accept_13_6_5_1_1_834 58 70 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 70 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 70 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 70 157 (accept_3_3 56 70 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  70 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 70 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 70 157 (Polychromatic418967fa.accept_24_6_22_13_1_8579 54 70 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 70 157 (accept_3_3 53 70 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 70 157 (Polychromatic418967fa.accept_12_4_10_1_1_706 52 70 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 70 157
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 70 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 70 157 (accept_3_3 50 70 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  70 157 (Polychromatic418967fa.accept_15_4_10_7_1_1356 49 70 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 70 157 (Polychromatic418967fa.accept_9_3_7_4_1_53 48 70 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 70 157 (accept_3_3 47 70 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 70 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 70 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 70 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 70 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 70 157 (accept_3_3 44 70 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  70 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 70 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 70 157 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 70 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 70 157 (accept_3_3 41 70 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 70 157 (Polychromatic418967fa.accept_11_7_4_3_1_302 40 70 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 70 157
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 70 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 70 157 (accept_3_3 38 70 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  70 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 70 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 70 157 (Polychromatic418967fa.accept_16_4_6_13_1_1874 36 70 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 70 157 (accept_3_3 35 70 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 70 157 (Polychromatic418967fa.accept_13_8_5_1_1_1381 34 70 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 70 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 70 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 70 157 (accept_3_3 32 70 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  70 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 70 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 70 157 (Polychromatic418967fa.accept_9_3_7_4_1_53 30 70 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 70 157 (accept_3_3 29 70 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 70 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 70 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 70 157
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 70 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 70 157 (accept_3_3 26 70 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  70 157 (Polychromatic418967fa.accept_13_12_5_1_1_1383 25 70 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 70 157 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 70 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 70 157 (accept_3_3 23 70 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 70 157 (Polychromatic418967fa.accept_13_9_5_1_1_1382 22 70 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 70 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 70 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 70 157 (accept_3_3 20 70 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  70 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 70 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 70 157 (Polychromatic418967fa.accept_11_7_4_3_1_302 18 70 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 70 157 (accept_3_3 17 70 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 70 157 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 70 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 70 157
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 70 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 70 157 (accept_3_3 14 70 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  70 157 (Polychromatic418967fa.accept_20_13_10_17_1_5510 13 70 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 70 157 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 70 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 70 157 (accept_3_3 11 70 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 70 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 70 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 70 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 70 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 70 157 (accept_3_3 8 70 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 70
  157 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 70 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 70 157 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 70 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 70 157 (accept_3_3 5 70 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 70 157 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 70 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 70 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 70
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 70 157 (accept_3_3 2 70 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 70 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 70
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70
  157)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 157 (allA_succ_of_accept 68 69
  157 (accept_3_3 68 69 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 69 157
  (Polychromatic418967fa.accept_7_4_6_3_1_271 67 69 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 69 157 (Polychromatic418967fa.accept_9_3_6_4_1_210 66 69 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 69 157 (accept_3_3 65 69 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 69 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 69 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 157 (Polychromatic418967fa.accept_12_3_9_1_1_290
  63 69 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 157 (accept_3_3 62
  69 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 157
  (Polychromatic418967fa.accept_9_7_6_4_1_483 61 69 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 69 157 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 69 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 69 157 (accept_3_3 59 69 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 69 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 69 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 157 (Polychromatic418967fa.accept_9_3_6_4_1_210 57
  69 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 157 (accept_3_3 56 69
  157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 69 157 (Polychromatic418967fa.accept_9_1_6_4_1_49
  55 69 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 69 157
  (Polychromatic418967fa.accept_19_16_12_5_1_8578 54 69 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 69 157 (accept_3_3 53 69 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  69 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 69 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 69 157 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 69 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 157 (accept_3_3 50 69 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 157 (Polychromatic418967fa.accept_13_10_4_1_1_2142 49 69 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 69 157
  (Polychromatic418967fa.accept_9_3_6_4_1_210 48 69 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 69 157 (accept_3_3 47 69 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  69 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 69 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 69 157 (Polychromatic418967fa.accept_19_7_12_5_1_7123 45 69 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 157 (accept_3_3 44 69 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 157 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 69 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 69 157
  (Polychromatic418967fa.accept_10_2_9_7_1_720 42 69 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 69 157 (accept_3_3 41 69 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  69 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 69 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 69 157 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 69 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 157 (accept_3_3 38 69 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 69 157 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 69 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 69 157
  (Polychromatic418967fa.accept_13_10_4_1_1_2142 36 69 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 69 157 (accept_3_3 35 69 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  69 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 69 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 69 157 (Polychromatic418967fa.accept_16_1_5_13_1_1025 33 69 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 157 (accept_3_3 32 69 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 157 (Polychromatic418967fa.accept_13_5_4_1_1_364 31 69 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 69 157
  (Polychromatic418967fa.accept_7_2_6_3_1_100 30 69 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 69 157 (accept_3_3 29 69 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  69 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 69 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 69 157 (Polychromatic418967fa.accept_12_3_9_1_1_290 27 69 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 157 (accept_3_3 26 69 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 157 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 69 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 69 157
  (Polychromatic418967fa.accept_14_10_13_3_1_2552 24 69 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 69 157 (accept_3_3 23 69 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  69 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 69 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 69 157 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 69 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 157 (accept_3_3 20 69 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 157 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 69 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 69 157
  (Polychromatic418967fa.accept_7_4_6_3_1_271 18 69 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 69 157 (accept_3_3 17 69 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  69 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 69 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 69 157 (Polychromatic418967fa.accept_12_3_9_1_1_290 15 69 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 157 (accept_3_3 14 69 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 157 (Polychromatic418967fa.accept_15_13_9_7_1_2194 13 69 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 69 157
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 69 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 69 157 (accept_3_3 11 69 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  69 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 69 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 69 157 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 69 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 157 (accept_3_3 8 69 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 157 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 69 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69 157
  (Polychromatic418967fa.accept_20_6_9_17_1_8577 6 69 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 157 (accept_3_3 5 69 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69
  157 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 69 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 69 157 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 69 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 157 (accept_3_3 2 69 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 69 157 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 69 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  157))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 157 (allA_of_3_1 68 68 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 67 157 (allA_succ_of_accept 66 67 157
  (Polychromatic418967fa.accept_4_2_3_1_1_2 66 67 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 157 (accept_3_3 65 67 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 157 (Polychromatic418967fa.accept_7_1_4_3_1_21 64 67 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 157 (Polychromatic418967fa.accept_14_7_11_3_1_5365 63 67 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 157 (accept_3_3 62 67 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 157 (Polychromatic418967fa.accept_13_9_2_1_1_813 61 67 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 157
  (Polychromatic418967fa.accept_19_3_10_5_1_4314 60 67 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 157 (accept_3_3 59 67 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 67 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 157 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 67 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 157 (accept_3_3 56 67 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 157 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 67 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 157
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 67 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 157 (accept_3_3 53 67 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 157 (Polychromatic418967fa.accept_19_14_10_5_1_3073 52 67 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 157 (Polychromatic418967fa.accept_13_12_2_1_1_2909 51 67 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 157 (accept_3_3 50 67 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 157 (Polychromatic418967fa.accept_14_7_11_3_1_5365 49 67
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 157
  (Polychromatic418967fa.accept_7_6_4_3_1_266 48 67 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 157 (accept_3_3 47 67 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 67 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 157 (Polychromatic418967fa.accept_13_6_2_1_1_2137 45 67 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 157 (accept_3_3 44 67 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 157 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 67 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 157
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 67 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 157 (accept_3_3 41 67 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 157 (Polychromatic418967fa.accept_16_8_3_13_1_7295 40 67 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 157 (Polychromatic418967fa.accept_17_5_16_4_1_4734 39 67 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 157 (accept_3_3 38 67 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 157 (Polychromatic418967fa.accept_17_3_16_4_1_2416 37 67
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 157
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 67 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 157 (accept_3_3 35 67 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 67 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 157 (Polychromatic418967fa.accept_16_1_3_13_1_2785 33 67 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 157 (accept_3_3 32 67 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 157 (Polychromatic418967fa.accept_16_15_3_13_1_2818 31 67
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 157
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 67 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 157 (accept_3_3 29 67 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 157 (Polychromatic418967fa.accept_20_8_7_17_1_8576 28 67 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 157 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 67 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 157 (accept_3_3 26 67 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 157 (Polychromatic418967fa.accept_13_12_2_1_1_2909 25 67 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 157
  (Polychromatic418967fa.accept_11_2_1_3_1_683 24 67 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 157 (accept_3_3 23 67 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 67 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 157 (Polychromatic418967fa.accept_14_7_11_3_1_5365 21 67 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 157 (accept_3_3 20 67 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 157 (Polychromatic418967fa.accept_13_6_2_1_1_2137 19 67 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 157
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 67 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 157 (accept_3_3 17 67 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 157 (Polychromatic418967fa.accept_13_3_2_1_1_2907 16 67 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 157 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 67 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 157 (accept_3_3 14 67 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 157 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 67 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 157
  (Polychromatic418967fa.accept_13_12_2_1_1_2909 12 67 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 157 (accept_3_3 11 67 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 67 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 157 (Polychromatic418967fa.accept_13_9_2_1_1_813 9 67 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 157 (accept_3_3 8 67 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 157 (Polychromatic418967fa.accept_14_7_11_3_1_5365 7 67 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 157
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 67 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 157 (accept_3_3 5 67 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  157 (Polychromatic418967fa.accept_20_4_7_17_1_5500 4 67 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 67 157 (Polychromatic418967fa.accept_13_3_2_1_1_2907 3 67 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 157 (accept_3_3 2 67 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 157 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 67 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  157))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 157 (allA_succ_of_accept 65 66
  157 (accept_3_3 65 66 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 66 157
  (Polychromatic418967fa.accept_9_1_3_4_1_47 64 66 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 66 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 66 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 66 157 (accept_3_3 62 66 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 66 157 (Polychromatic418967fa.accept_9_7_3_4_1_218 61 66 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 66 157 (Polychromatic418967fa.accept_9_6_3_4_1_477 60
  66 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 66 157 (accept_3_3 59 66
  157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 66 157
  (Polychromatic418967fa.accept_15_13_6_7_1_1369 58 66 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 66 157 (Polychromatic418967fa.accept_15_12_6_7_1_1353 57 66 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 66 157 (accept_3_3 56 66 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 66 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 66 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 66 157
  (Polychromatic418967fa.accept_21_12_3_10_1_8575 54 66 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 66 157 (accept_3_3 53 66 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  66 157 (Polychromatic418967fa.accept_9_7_3_4_1_218 52 66 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 66 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 66 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 66 157 (accept_3_3 50 66 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 157 (Polychromatic418967fa.accept_14_7_10_3_1_1034 49 66 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 66 157
  (Polychromatic418967fa.accept_14_6_10_3_1_1038 48 66 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 66 157 (accept_3_3 47 66 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  66 157 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 66 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 66 157 (Polychromatic418967fa.accept_17_11_15_4_1_2415 45 66 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 66 157 (accept_3_3 44 66 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 66 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 66 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 66 157
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 66 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 66 157 (accept_3_3 41 66 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  66 157 (Polychromatic418967fa.accept_23_17_20_19_1_8574 40 66 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 66 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 66 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 66 157 (accept_3_3 38 66 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 66 157 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 66 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 66 157
  (Polychromatic418967fa.accept_17_2_15_4_1_4723 36 66 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 66 157 (accept_3_3 35 66 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  66 157 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 66 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 66 157 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 66 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 66 157 (accept_3_3 32 66 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 66 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 66 157
  (Polychromatic418967fa.accept_21_9_3_10_1_8573 30 66 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 66 157 (accept_3_3 29 66 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  66 157 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 66 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 66 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 66 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 66 157 (accept_3_3 26 66 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 157 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 66 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 66 157
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 66 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 66 157 (accept_3_3 23 66 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  66 157 (Polychromatic418967fa.accept_21_1_3_10_1_5401 22 66 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 66 157 (Polychromatic418967fa.accept_10_1_6_7_1_710 21 66 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 66 157 (accept_3_3 20 66 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 66 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 66 157
  (Polychromatic418967fa.accept_19_18_9_5_1_8542 18 66 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 66 157 (accept_3_3 17 66 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  66 157 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 66 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 66 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 66 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 66 157 (accept_3_3 14 66 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 157 (Polychromatic418967fa.accept_10_3_6_7_1_2188 13 66 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 66 157
  (Polychromatic418967fa.accept_15_12_6_7_1_1353 12 66 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 66 157 (accept_3_3 11 66 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  66 157 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 66 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 66 157 (Polychromatic418967fa.accept_20_9_6_17_1_1654 9 66 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 66 157 (accept_3_3 8 66 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 66 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 66 157
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 66 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 66 157 (accept_3_3 5 66 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66
  157 (Polychromatic418967fa.accept_19_4_9_5_1_8572 4 66 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 66 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 66 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 66 157 (accept_3_3 2 66 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 157 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 66 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  157)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 157 (allA_of_3_1 65 65 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 64 157 (allA_succ_of_accept 63 64 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 64 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 64 157 (accept_3_3 62 64 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  64 157 (Polychromatic418967fa.accept_7_5_1_3_1_103 61 64 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 64 157 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 64 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 64 157 (accept_3_3 59 64 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 64 157 (Polychromatic418967fa.accept_7_2_1_3_1_102 58 64 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 64 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 64 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 64 157 (accept_3_3 56 64 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  64 157 (Polychromatic418967fa.accept_15_10_4_7_1_3127 55 64 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 64 157 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 64 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 64 157 (accept_3_3 53 64 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 64 157 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 64 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 64 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 64 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 64 157 (accept_3_3 50 64 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  64 157 (Polychromatic418967fa.accept_21_7_1_10_1_8571 49 64 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 64 157 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 64 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 64 157 (accept_3_3 47 64 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 64 157 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 64 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 64 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 64 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 64 157 (accept_3_3 44 64 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  64 157 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 64 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 64 157 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 64 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 64 157 (accept_3_3 41 64 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 64 157 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 64 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 64 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 64 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 64 157 (accept_3_3 38 64 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  64 157 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 64 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 64 157 (Polychromatic418967fa.accept_19_17_7_5_1_1883 36 64 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 64 157 (accept_3_3 35 64 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 64 157 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 64 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 64 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 64 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 64 157 (accept_3_3 32 64 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  64 157 (Polychromatic418967fa.accept_10_1_4_7_1_374 31 64 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 64 157 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 64 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 64 157 (accept_3_3 29 64 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 64 157 (Polychromatic418967fa.accept_11_6_9_3_1_1103 28 64 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 64 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 64 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 64 157 (accept_3_3 26 64 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  64 157 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 64 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 64 157 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 64 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 64 157 (accept_3_3 23 64 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 64 157 (Polychromatic418967fa.accept_10_2_4_7_1_352 22 64 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 64 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 64 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 64 157 (accept_3_3 20 64 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  64 157 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 64 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 64 157 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 64 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 64 157 (accept_3_3 17 64 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 64 157 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 64 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 64 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 64 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 64 157 (accept_3_3 14 64 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  64 157 (Polychromatic418967fa.accept_10_3_4_7_1_353 13 64 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 64 157 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 64 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 64 157 (accept_3_3 11 64 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 64 157 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 64 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 64 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 64 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 64 157 (accept_3_3 8 64 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 64
  157 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 64 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 64 157 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 64 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 64 157 (accept_3_3 5 64 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 64 157 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 64 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 64 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 64
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 64 157 (accept_3_3 2 64 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 64 157 (Polychromatic418967fa.accept_10_1_4_7_1_374 1
  64 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64
  157)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 157 (allA_succ_of_accept 62 63 157
  (accept_3_3 62 63 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 63 157
  (Polychromatic418967fa.accept_11_6_8_3_1_2236 61 63 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 63 157 (Polychromatic418967fa.accept_11_5_8_3_1_66 60 63 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 63 157 (accept_3_3 59 63 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 63 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 63 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 157 (Polychromatic418967fa.accept_12_9_3_1_1_303
  57 63 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 157 (accept_3_3 56
  63 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 63 157
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 55 63 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 63 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 63 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 63 157 (accept_3_3 53 63 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 63 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 63 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 157
  (Polychromatic418967fa.accept_13_12_11_1_1_2920 51 63 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 63 157 (accept_3_3 50 63 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  63 157 (Polychromatic418967fa.accept_11_5_8_3_1_66 49 63 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 63 157 (Polychromatic418967fa.accept_13_9_11_1_1_1375 48 63 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 63 157 (accept_3_3 47 63 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 63 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 157
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 63 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 63 157 (accept_3_3 44 63 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  63 157 (Polychromatic418967fa.accept_17_9_12_4_1_3468 43 63 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 63 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 63 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 63 157 (accept_3_3 41 63 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 63 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 157
  (Polychromatic418967fa.accept_11_6_8_3_1_2236 39 63 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 63 157 (accept_3_3 38 63 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  63 157 (Polychromatic418967fa.accept_19_18_6_5_1_4321 37 63 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 63 157 (Polychromatic418967fa.accept_10_6_3_7_1_2197 36 63 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 63 157 (accept_3_3 35 63 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 63 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 157
  (Polychromatic418967fa.accept_12_9_3_1_1_303 33 63 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 63 157 (accept_3_3 32 63 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  63 157 (Polychromatic418967fa.accept_24_7_15_13_1_8570 31 63 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 63 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 63 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 157 (accept_3_3 29 63 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 63 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 157
  (Polychromatic418967fa.accept_11_5_8_3_1_66 27 63 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 63 157 (accept_3_3 26 63 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  63 157 (Polychromatic418967fa.accept_10_5_3_7_1_1108 25 63 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 63 157 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 63 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 157 (accept_3_3 23 63 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 63 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 157
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 63 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 63 157 (accept_3_3 20 63 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  63 157 (Polychromatic418967fa.accept_15_4_3_7_1_713 19 63 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 63 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 63 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 157 (accept_3_3 17 63 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 63 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 157
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 63 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 63 157 (accept_3_3 14 63 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  63 157 (Polychromatic418967fa.accept_23_13_17_19_1_8551 13 63 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 63 157 (Polychromatic418967fa.accept_13_12_11_1_1_2920 12 63 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 157 (accept_3_3 11 63 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 63 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 157
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 63 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 63 157 (accept_3_3 8 63 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63
  157 (Polychromatic418967fa.accept_13_7_11_1_1_2903 7 63 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 63 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 63 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 157 (accept_3_3 5 63 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 63 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 157
  (Polychromatic418967fa.accept_13_3_11_1_1_2122 3 63 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 63 157 (accept_3_3 2 63 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63
  157 (Polychromatic418967fa.accept_19_1_6_5_1_4319 1 63 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 63 157))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 157
  (allA_of_3_1 62 62 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 61 157 (allA_succ_of_accept 60 61 157
  (Polychromatic418967fa.accept_9_6_7_4_1_212 60 61 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 157 (accept_3_3 59 61 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 157 (Polychromatic418967fa.accept_7_2_5_3_1_98 58 61 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 157 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 61 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 157 (accept_3_3 56 61 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 61 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 157
  (Polychromatic418967fa.accept_10_4_1_7_1_371 54 61 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 157 (accept_3_3 53 61 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 157 (Polychromatic418967fa.accept_11_8_6_3_1_661 52 61 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 157 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 61 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 157 (accept_3_3 50 61 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 157 (Polychromatic418967fa.accept_13_10_9_1_1_5609 49 61 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 157
  (Polychromatic418967fa.accept_9_3_7_4_1_53 48 61 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 157 (accept_3_3 47 61 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 61 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 157 (Polychromatic418967fa.accept_13_6_9_1_1_5604 45 61 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 157 (accept_3_3 44 61 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 157 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 61 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 157
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 61 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 157 (accept_3_3 41 61 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 157 (Polychromatic418967fa.accept_14_12_5_3_1_1011 40 61 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 157 (Polychromatic418967fa.accept_9_3_7_4_1_53 39 61 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 157 (accept_3_3 38 61 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 157 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 61 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 157
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 61 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 157 (accept_3_3 35 61 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 157 (Polychromatic418967fa.accept_10_4_1_7_1_371 34 61 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 157 (Polychromatic418967fa.accept_9_6_7_4_1_212 33 61 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 157 (accept_3_3 32 61 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 157 (Polychromatic418967fa.accept_11_9_6_3_1_1668 31 61 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 157
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 61 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 157 (accept_3_3 29 61 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 61 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 157 (Polychromatic418967fa.accept_19_8_4_5_1_8569 27 61 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 157 (accept_3_3 26 61 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 157 (Polychromatic418967fa.accept_15_10_1_7_1_5207 25 61 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 157
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 61 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 157 (accept_3_3 23 61 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 157 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 61 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 157 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 61 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 157 (accept_3_3 20 61 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 61 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 157
  (Polychromatic418967fa.accept_13_5_9_1_1_1405 18 61 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 157 (accept_3_3 17 61 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 157 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 61 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 157 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 61 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 157 (accept_3_3 14 61 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 157 (Polychromatic418967fa.accept_25_13_11_7_1_8568 13 61 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 157
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 61 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 157 (accept_3_3 11 61 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 61 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 157 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 61 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 157 (accept_3_3 8 61 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 157 (Polychromatic418967fa.accept_21_7_19_10_1_8567 7 61 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 157
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 61 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 157 (accept_3_3 5 61 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  157 (Polychromatic418967fa.accept_10_4_1_7_1_371 4 61 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 157 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 61 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 157 (accept_3_3 2 61 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 157 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 61 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 157)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 157 (allA_succ_of_accept 59 60 157 (accept_3_3 59 60 157 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 60 157 (Polychromatic418967fa.accept_13_6_8_1_1_2913 58 60 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 60 157 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 60 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 60 157 (accept_3_3 56 60 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 60 157 (Polychromatic418967fa.accept_7_6_4_3_1_266 55
  60 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 60 157
  (Polychromatic418967fa.accept_19_16_3_5_1_5684 54 60 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 60 157 (accept_3_3 53 60 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  60 157 (Polychromatic418967fa.accept_9_7_6_4_1_483 52 60 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 60 157 (Polychromatic418967fa.accept_13_12_8_1_1_825 51 60 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 60 157 (accept_3_3 50 60 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 60 157 (Polychromatic418967fa.accept_8_1_4_5_1_48 49 60 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 60 157
  (Polychromatic418967fa.accept_7_6_4_3_1_266 48 60 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 60 157 (accept_3_3 47 60 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  60 157 (Polychromatic418967fa.accept_9_1_6_4_1_49 46 60 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 60 157 (Polychromatic418967fa.accept_13_6_8_1_1_2913 45 60 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 60 157 (accept_3_3 44 60 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 157 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 60 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 60 157
  (Polychromatic418967fa.accept_16_10_12_13_1_4950 42 60 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 60 157 (accept_3_3 41 60 157 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 60 157 (Polychromatic418967fa.accept_16_8_12_13_1_3851 40 60 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 60 157 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 60 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 60 157 (accept_3_3 38 60 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 157 (Polychromatic418967fa.accept_9_1_6_4_1_49 37
  60 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 60 157
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 60 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 60 157 (accept_3_3 35 60 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  60 157 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 60 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 60 157 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 60 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 60 157 (accept_3_3 32 60 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 157 (Polychromatic418967fa.accept_13_5_8_1_1_2161 31 60 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 60 157
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 60 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 60 157 (accept_3_3 29 60 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  60 157 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 60 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 60 157 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 60 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 60 157 (accept_3_3 26 60 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 60 157 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 60 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 60 157
  (Polychromatic418967fa.accept_13_11_8_1_1_3815 24 60 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 60 157 (accept_3_3 23 60 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  60 157 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 60 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 60 157 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 60 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 60 157 (accept_3_3 20 60 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 157 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 60 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 60 157
  (Polychromatic418967fa.accept_13_5_8_1_1_2161 18 60 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 60 157 (accept_3_3 17 60 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  60 157 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 60 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 60 157 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 60 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 60 157 (accept_3_3 14 60 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 157 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 60 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 60 157
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 60 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 60 157 (accept_3_3 11 60 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  60 157 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 60 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 60 157 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 60 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 60 157 (accept_3_3 8 60 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 157 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 60 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 60 157
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 60 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 60 157 (accept_3_3 5 60 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 60
  157 (Polychromatic418967fa.accept_16_4_12_13_1_990 4 60 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 60 157 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 60 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 60 157 (accept_3_3 2 60 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 157 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 60 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  157)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 157 (allA_of_3_1 59 59 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 58 157 (allA_succ_of_accept 57 58 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 58 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 58 157 (accept_3_3 56 58 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  58 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 58 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 58 157 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 58 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 58 157 (accept_3_3 53 58 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 58 157 (Polychromatic418967fa.accept_12_4_10_1_1_706 52 58 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 58 157
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 58 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 58 157 (accept_3_3 50 58 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  58 157 (Polychromatic418967fa.accept_10_9_8_7_1_714 49 58 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 58 157 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 58 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 58 157 (accept_3_3 47 58 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 58 157 (Polychromatic418967fa.accept_13_7_6_1_1_368 46 58 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 58 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 58 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 58 157 (accept_3_3 44 58 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  58 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 58 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 58 157 (Polychromatic418967fa.accept_13_3_6_1_1_3797 42 58 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 58 157 (accept_3_3 41 58 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 58 157 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 58 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 58 157
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 58 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 58 157 (accept_3_3 38 58 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  58 157 (Polychromatic418967fa.accept_16_5_10_13_1_6042 37 58 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 58 157 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 58 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 58 157 (accept_3_3 35 58 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 58 157 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 58 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 58 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 58 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 58 157 (accept_3_3 32 58 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  58 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 58 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 58 157 (Polychromatic418967fa.accept_16_14_10_13_1_2768 30 58 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 58 157 (accept_3_3 29 58 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 58 157 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 58 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 58 157
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 58 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 58 157 (accept_3_3 26 58 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  58 157 (Polychromatic418967fa.accept_10_5_8_7_1_2174 25 58 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 58 157 (Polychromatic418967fa.accept_15_9_13_7_1_1361 24 58 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 58 157 (accept_3_3 23 58 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 58 157 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 58 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 58 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 58 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 58 157 (accept_3_3 20 58 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  58 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 58 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 58 157 (Polychromatic418967fa.accept_13_5_6_1_1_822 18 58 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 58 157 (accept_3_3 17 58 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 58 157 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 58 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 58 157
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 58 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 58 157 (accept_3_3 14 58 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  58 157 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 58 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 58 157 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 58 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 58 157 (accept_3_3 11 58 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 58 157 (Polychromatic418967fa.accept_18_10_4_13_1_3296 10 58 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 58 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 58 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 58 157 (accept_3_3 8 58 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 58
  157 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 58 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 58 157 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 58 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 58 157 (accept_3_3 5 58 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 58 157 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 58 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 58 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 58
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 58 157 (accept_3_3 2 58 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 58 157 (Polychromatic418967fa.accept_7_1_2_3_1_257 1
  58 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  157)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 157 (allA_succ_of_accept 56 57 157
  (accept_3_3 56 57 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 157
  (Polychromatic418967fa.accept_9_1_3_4_1_47 55 57 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 57 157 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 57 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 157 (accept_3_3 53 57 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 57 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 57 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 157 (Polychromatic418967fa.accept_7_2_1_3_1_102 51
  57 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 157 (accept_3_3 50 57
  157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 157
  (Polychromatic418967fa.accept_15_4_12_7_1_3115 49 57 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 57 157 (Polychromatic418967fa.accept_13_9_5_1_1_1382 48 57 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 57 157 (accept_3_3 47 57 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 57 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 57 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 157 (Polychromatic418967fa.accept_11_1_2_3_1_688
  45 57 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 157 (accept_3_3 44
  57 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 157
  (Polychromatic418967fa.accept_9_7_3_4_1_218 43 57 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 57 157 (Polychromatic418967fa.accept_9_6_3_4_1_477 42 57 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 57 157 (accept_3_3 41 57 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 57 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 57 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 157 (Polychromatic418967fa.accept_7_4_1_3_1_277 39
  57 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 157 (accept_3_3 38 57
  157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 157
  (Polychromatic418967fa.accept_7_2_1_3_1_102 37 57 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 57 157 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 57 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 57 157 (accept_3_3 35 57 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 57 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 57 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 157 (Polychromatic418967fa.accept_7_5_1_3_1_103 33
  57 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 157 (accept_3_3 32 57
  157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 157
  (Polychromatic418967fa.accept_23_8_11_19_1_8566 31 57 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 57 157 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 57 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 57 157 (accept_3_3 29 57 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 57 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 57 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 157 (Polychromatic418967fa.accept_12_3_9_1_1_290
  27 57 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 157 (accept_3_3 26
  57 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 157
  (Polychromatic418967fa.accept_7_4_1_3_1_277 25 57 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 57 157 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 57 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 57 157 (accept_3_3 23 57 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 57 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 57 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 157 (Polychromatic418967fa.accept_13_8_5_1_1_1381
  21 57 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 157 (accept_3_3 20
  57 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 157
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 57 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 57 157 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 57 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 57 157 (accept_3_3 17 57 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 57 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 57 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 157 (Polychromatic418967fa.accept_9_6_3_4_1_477 15
  57 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 157 (accept_3_3 14 57
  157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 157
  (Polychromatic418967fa.accept_28_13_1_17_1_8565 13 57 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 57 157 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 57 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 57 157 (accept_3_3 11 57 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 57 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 57 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 157 (Polychromatic418967fa.accept_7_2_1_3_1_102 9
  57 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 157 (accept_3_3 8 57 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 157 (Polychromatic418967fa.accept_9_7_3_4_1_218 7
  57 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 157
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 57 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 157 (accept_3_3 5 57 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57
  157 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 57 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 57 157 (Polychromatic418967fa.accept_12_3_9_1_1_290 3 57 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 157 (accept_3_3 2 57 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 57 157 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 57 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 157)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 157 (allA_of_3_1 56 56 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 55 157
  (allA_succ_of_accept 54 55 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 55 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 157 (accept_3_3 53 55 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 55 157 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 55 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 157 (Polychromatic418967fa.accept_7_2_6_3_1_100 51
  55 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 55 157 (accept_3_3 50 55
  157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 55 157
  (Polychromatic418967fa.accept_15_4_10_7_1_1356 49 55 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 55 157 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 55 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 157 (accept_3_3 47 55 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 55 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 55 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 55 157 (Polychromatic418967fa.accept_13_6_3_1_1_1413
  45 55 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 55 157 (accept_3_3 44
  55 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 157
  (Polychromatic418967fa.accept_9_7_1_4_1_217 43 55 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 55 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 55 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 55 157 (accept_3_3 41 55 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 55 157 (Polychromatic418967fa.accept_19_2_17_5_1_5643 40 55 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 55 157
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 55 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 55 157 (accept_3_3 38 55 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  55 157 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 55 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 55 157 (Polychromatic418967fa.accept_16_4_7_13_1_2795 36 55 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 55 157 (accept_3_3 35 55 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 55 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 55 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 55 157
  (Polychromatic418967fa.accept_9_6_1_4_1_474 33 55 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 55 157 (accept_3_3 32 55 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  55 157 (Polychromatic418967fa.accept_13_5_3_1_1_1398 31 55 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 55 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 55 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 55 157 (accept_3_3 29 55 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 157 (Polychromatic418967fa.accept_10_8_5_7_1_358 28 55 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 157
  (Polychromatic418967fa.accept_15_12_10_7_1_1357 27 55 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 55 157 (accept_3_3 26 55 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  55 157 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 55 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 55 157 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 55 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 55 157 (accept_3_3 23 55 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 55 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 55 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 157
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 55 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 55 157 (accept_3_3 20 55 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  55 157 (Polychromatic418967fa.accept_13_6_3_1_1_1413 19 55 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 55 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 55 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 157 (accept_3_3 17 55 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 55 157 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 55 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 55 157
  (Polychromatic418967fa.accept_9_6_1_4_1_474 15 55 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 55 157 (accept_3_3 14 55 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  55 157 (Polychromatic418967fa.accept_10_3_5_7_1_330 13 55 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 55 157 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 55 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 55 157 (accept_3_3 11 55 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 55 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 55 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 55 157
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 55 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 55 157 (accept_3_3 8 55 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55
  157 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 55 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 55 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 55 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 55 157 (accept_3_3 5 55 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 55 157 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 55 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 157 (Polychromatic418967fa.accept_9_3_1_4_1_216 3
  55 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 157 (accept_3_3 2 55 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55 157 (Polychromatic418967fa.accept_15_1_10_7_1_4087
  1 55 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55
  157))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 54 157 (allA_succ_of_accept 53 54 157
  (accept_3_3 53 54 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 54 157
  (Polychromatic418967fa.accept_10_2_4_7_1_352 52 54 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 54 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 54 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 54 157 (accept_3_3 50 54 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 54 157 (Polychromatic418967fa.accept_19_11_16_5_1_5667 49 54 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 157
  (Polychromatic418967fa.accept_13_9_2_1_1_813 48 54 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 54 157 (accept_3_3 47 54 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  54 157 (Polychromatic418967fa.accept_15_1_9_7_1_3130 46 54 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 54 157 (Polychromatic418967fa.accept_13_6_2_1_1_2137 45 54 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 54 157 (accept_3_3 44 54 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 54 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 157
  (Polychromatic418967fa.accept_10_2_4_7_1_352 42 54 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 54 157 (accept_3_3 41 54 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  54 157 (Polychromatic418967fa.accept_11_7_10_3_1_633 40 54 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 54 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 54 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 54 157 (accept_3_3 38 54 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 157 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 54 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 54 157
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 54 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 54 157 (accept_3_3 35 54 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  54 157 (Polychromatic418967fa.accept_23_11_8_19_1_8564 34 54 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 54 157 (Polychromatic418967fa.accept_10_3_4_7_1_353 33 54 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 54 157 (accept_3_3 32 54 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 54 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 54 157
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 54 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 54 157 (accept_3_3 29 54 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  54 157 (Polychromatic418967fa.accept_15_13_9_7_1_2194 28 54 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 54 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 54 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 157 (accept_3_3 26 54 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 157 (Polychromatic418967fa.accept_13_12_2_1_1_2909 25 54 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 54 157
  (Polychromatic418967fa.accept_17_7_3_4_1_8563 24 54 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 54 157 (accept_3_3 23 54 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  54 157 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 54 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 54 157 (Polychromatic418967fa.accept_10_1_4_7_1_374 21 54 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 157 (accept_3_3 20 54 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 54 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 54 157
  (Polychromatic418967fa.accept_11_7_10_3_1_633 18 54 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 54 157 (accept_3_3 17 54 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  54 157 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 54 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 54 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 54 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 157 (accept_3_3 14 54 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 157 (Polychromatic418967fa.accept_10_3_4_7_1_353 13 54 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 54 157
  (Polychromatic418967fa.accept_10_2_4_7_1_352 12 54 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 54 157 (accept_3_3 11 54 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  54 157 (Polychromatic418967fa.accept_19_10_16_5_1_8562 10 54 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 54 157 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 54 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 157 (accept_3_3 8 54 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 54 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54 157
  (Polychromatic418967fa.accept_13_6_2_1_1_2137 6 54 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 54 157 (accept_3_3 5 54 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54
  157 (Polychromatic418967fa.accept_16_4_6_13_1_1874 4 54 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 54 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 54 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 157 (accept_3_3 2 54 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 157 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 54 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  157)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 157 (allA_of_3_1 53 53 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 52 157 (allA_succ_of_accept 51 52 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 52
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 52 157 (accept_3_3 50 52 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 52 157 (Polychromatic418967fa.accept_8_1_4_5_1_48 49
  52 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 157
  (Polychromatic418967fa.accept_9_3_7_4_1_53 48 52 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 52 157 (accept_3_3 47 52 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  52 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 52 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 52 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 52 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 52 157 (accept_3_3 44 52 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 52 157 (Polychromatic418967fa.accept_25_18_2_7_1_8560 43 52 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 52 157
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 52 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 52 157 (accept_3_3 41 52 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  52 157 (Polychromatic418967fa.accept_16_8_4_13_1_1014 40 52 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 52 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 52 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 52 157 (accept_3_3 38 52 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 52 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 52 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 52 157
  (Polychromatic418967fa.accept_19_17_14_5_1_8561 36 52 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 52 157 (accept_3_3 35 52 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  52 157 (Polychromatic418967fa.accept_10_4_2_7_1_373 34 52 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 52 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 52 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 52 157 (accept_3_3 32 52 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 52 157 (Polychromatic418967fa.accept_17_14_1_4_1_2485 31 52 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 52 157
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 52 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 52 157 (accept_3_3 29 52 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  52 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 52 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 52 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 52 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 52 157 (accept_3_3 26 52 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 52 157 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 52 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 52 157
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 52 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 52 157 (accept_3_3 23 52 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  52 157 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 52 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 52 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 52 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 52 157 (accept_3_3 20 52 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 52 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 52 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 52 157
  (Polychromatic418967fa.accept_25_18_2_7_1_8560 18 52 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 52 157 (accept_3_3 17 52 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  52 157 (Polychromatic418967fa.accept_11_5_8_3_1_66 16 52 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 52 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 52 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 52 157 (accept_3_3 14 52 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 52 157 (Polychromatic418967fa.accept_14_13_10_3_1_1037 13 52 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 52 157
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 52 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 52 157 (accept_3_3 11 52 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  52 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 52 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 52 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 52 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 52 157 (accept_3_3 8 52 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 52 157 (Polychromatic418967fa.accept_14_7_10_3_1_1034 7 52 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 52 157
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 52 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 52 157 (accept_3_3 5 52 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 52
  157 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 52 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 52 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 52 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 52 157 (accept_3_3 2 52 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 52 157 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 52 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52 157))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 51 157 (allA_succ_of_accept 50 51 157 (accept_3_3 50 51 157 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 157 (Polychromatic418967fa.accept_16_1_3_13_1_2785 49 51 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 51 157 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 51 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 157 (accept_3_3 47 51 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 46
  51 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 157
  (Polychromatic418967fa.accept_12_9_3_1_1_303 45 51 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 51 157 (accept_3_3 44 51 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  51 157 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 51 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 51 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 51 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 157 (accept_3_3 41 51 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 51 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 157
  (Polychromatic418967fa.accept_9_3_6_4_1_210 39 51 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 51 157 (accept_3_3 38 51 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  51 157 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 51 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 51 157 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 51 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 51 157 (accept_3_3 35 51 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 51 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 157
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 51 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 51 157 (accept_3_3 32 51 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  51 157 (Polychromatic418967fa.accept_13_5_12_1_1_2123 31 51 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 51 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 51 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 157 (accept_3_3 29 51 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 51 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 157
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 51 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 51 157 (accept_3_3 26 51 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  51 157 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 51 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 51 157 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 51 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 51 157 (accept_3_3 23 51 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 51 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 157
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 51 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 51 157 (accept_3_3 20 51 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  51 157 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 51 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 51 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 51 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 51 157 (accept_3_3 17 51 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 51 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 157
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 51 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 51 157 (accept_3_3 14 51 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  51 157 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 51 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 51 157 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 51 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 157 (accept_3_3 11 51 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 51 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 157
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 51 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 51 157 (accept_3_3 8 51 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51
  157 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 51 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 51 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 51 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 51 157 (accept_3_3 5 51 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 51 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 51 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 51 157 (Polychromatic418967fa.accept_9_3_6_4_1_210 3
  51 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 157 (accept_3_3 2 51 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 157 (Polychromatic418967fa.accept_7_1_2_3_1_257 1
  51 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51
  157))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 157 (allA_of_3_1 50 50 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 49 157 (allA_succ_of_accept 48 49 157 (Polychromatic418967fa.accept_10_8_9_7_1_1118 48
  49 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 157 (accept_3_3 47 49
  157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 49 157
  (Polychromatic418967fa.accept_14_4_7_3_1_1718 46 49 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 49 157 (Polychromatic418967fa.accept_17_11_15_4_1_2415 45 49 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 157 (accept_3_3 44 49 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 49 157 (Polychromatic418967fa.accept_13_4_10_1_1_1390 43 49 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 49 157
  (Polychromatic418967fa.accept_10_2_9_7_1_720 42 49 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 49 157 (accept_3_3 41 49 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  49 157 (Polychromatic418967fa.accept_15_10_4_7_1_3127 40 49 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 49 157 (Polychromatic418967fa.accept_14_11_7_3_1_3416 39 49 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 157 (accept_3_3 38 49 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 49 157 (Polychromatic418967fa.accept_13_11_10_1_1_1409 37 49
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 157
  (Polychromatic418967fa.accept_8_4_1_5_1_186 36 49 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 49 157 (accept_3_3 35 49 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  49 157 (Polychromatic418967fa.accept_19_15_11_5_1_5713 34 49 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 49 157 (Polychromatic418967fa.accept_15_3_4_7_1_1352 33 49 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 157 (accept_3_3 32 49 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 157 (Polychromatic418967fa.accept_19_12_11_5_1_950 31 49 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 157
  (Polychromatic418967fa.accept_11_8_5_3_1_694 30 49 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 49 157 (accept_3_3 29 49 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  49 157 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 49 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 49 157 (Polychromatic418967fa.accept_15_12_4_7_1_3097 27 49 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 49 157 (accept_3_3 26 49 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 49 157 (Polychromatic418967fa.accept_14_11_7_3_1_3416 25 49
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 157
  (Polychromatic418967fa.accept_13_11_10_1_1_1409 24 49 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 49 157 (accept_3_3 23 49 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  49 157 (Polychromatic418967fa.accept_10_2_9_7_1_720 22 49 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 49 157 (Polychromatic418967fa.accept_16_5_1_13_1_1053 21 49 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 49 157 (accept_3_3 20 49 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 157 (Polychromatic418967fa.accept_11_8_5_3_1_694 19 49 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 157
  (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 49 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 49 157 (accept_3_3 17 49 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  49 157 (Polychromatic418967fa.accept_17_16_15_4_1_8559 16 49 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 49 157 (Polychromatic418967fa.accept_19_15_11_5_1_5713 15 49 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 49 157 (accept_3_3 14 49 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 49 157 (Polychromatic418967fa.accept_19_13_11_5_1_5692 13 49
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 157
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 49 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 49 157 (accept_3_3 11 49 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  49 157 (Polychromatic418967fa.accept_14_10_7_3_1_1022 10 49 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 49 157 (Polychromatic418967fa.accept_13_9_10_1_1_1389 9 49 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 157 (accept_3_3 8 49 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 49 157 (Polychromatic418967fa.accept_20_7_9_17_1_8558 7 49 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 49 157
  (Polychromatic418967fa.accept_19_6_11_5_1_5628 6 49 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 49 157 (accept_3_3 5 49 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49
  157 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 49 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 49 157 (Polychromatic418967fa.accept_15_3_4_7_1_1352 3 49 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 157 (accept_3_3 2 49 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 49 157 (Polychromatic418967fa.accept_21_1_7_10_1_2596 1 49 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 157))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  48 157 (allA_succ_of_accept 47 48 157 (accept_3_3 47 48 157 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 48 157 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 48 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 48 157 (Polychromatic418967fa.accept_10_5_8_7_1_2174 45 48 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 48 157 (accept_3_3 44 48 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 157 (Polychromatic418967fa.accept_9_7_3_4_1_218 43
  48 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 48 157
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 48 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 48 157 (accept_3_3 41 48 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  48 157 (Polychromatic418967fa.accept_11_7_4_3_1_302 40 48 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 48 157 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 48 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 48 157 (accept_3_3 38 48 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 157 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 48 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 157
  (Polychromatic418967fa.accept_13_10_9_1_1_5609 36 48 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 48 157 (accept_3_3 35 48 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  48 157 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 48 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 48 157 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 48 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 48 157 (accept_3_3 32 48 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 157 (Polychromatic418967fa.accept_13_5_9_1_1_1405 31 48 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 157
  (Polychromatic418967fa.accept_7_2_6_3_1_100 30 48 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 48 157 (accept_3_3 29 48 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  48 157 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 48 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 48 157 (Polychromatic418967fa.accept_15_12_3_7_1_4123 27 48 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 48 157 (accept_3_3 26 48 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 157 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 48 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 157
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 48 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 48 157 (accept_3_3 23 48 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  48 157 (Polychromatic418967fa.accept_19_3_10_5_1_4314 22 48 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 48 157 (Polychromatic418967fa.accept_13_8_9_1_1_2147 21 48 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 48 157 (accept_3_3 20 48 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 157 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 48 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 48 157
  (Polychromatic418967fa.accept_7_4_6_3_1_271 18 48 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 48 157 (accept_3_3 17 48 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  48 157 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 48 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 48 157 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 48 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 48 157 (accept_3_3 14 48 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 157 (Polychromatic418967fa.accept_17_13_14_4_1_2468 13 48 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 48 157
  (Polychromatic418967fa.accept_15_12_3_7_1_4123 12 48 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 48 157 (accept_3_3 11 48 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  48 157 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 48 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 48 157 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 48 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 48 157 (accept_3_3 8 48 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 157 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 48 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 157
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 48 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 48 157 (accept_3_3 5 48 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48
  157 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 48 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 48 157 (Polychromatic418967fa.accept_18_3_12_13_1_3307 3 48 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 48 157 (accept_3_3 2 48 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 48 157 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 48 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48 157)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  47 157 (allA_of_3_1 47 47 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 46 157 (allA_succ_of_accept 45 46
  157 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 46 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 46 157 (accept_3_3 44 46 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  46 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 46 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 46 157 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 46 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 157 (accept_3_3 41 46 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 46 157 (Polychromatic418967fa.accept_12_4_10_1_1_706 40 46 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 46 157
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 46 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 46 157 (accept_3_3 38 46 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  46 157 (Polychromatic418967fa.accept_13_11_7_1_1_1386 37 46 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 46 157 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 46 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 46 157 (accept_3_3 35 46 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 46 157 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 46 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 46 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 46 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 46 157 (accept_3_3 32 46 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  46 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 46 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 46 157 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 46 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 46 157 (accept_3_3 29 46 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 46 157 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 46 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 46 157
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 46 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 46 157 (accept_3_3 26 46 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  46 157 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 46 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 46 157 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 46 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 157 (accept_3_3 23 46 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 46 157 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 46 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 46 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 46 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 46 157 (accept_3_3 20 46 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  46 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 46 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 46 157 (Polychromatic418967fa.accept_29_18_17_12_1_8557 18 46 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 157 (accept_3_3 17 46 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 46 157 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 46 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 46 157
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 46 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 46 157 (accept_3_3 14 46 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  46 157 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 46 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 46 157 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 46 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 46 157 (accept_3_3 11 46 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 46 157 (Polychromatic418967fa.accept_15_10_1_7_1_5207 10 46 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 46 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 46 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 46 157 (accept_3_3 8 46 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 46
  157 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 46 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 46 157 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 46 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 46 157 (accept_3_3 5 46 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 46 157 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 46 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 46 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 46
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 46 157 (accept_3_3 2 46 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 46 157 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 46
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  157)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 157 (allA_succ_of_accept 44 45 157 (accept_3_3 44 45
  157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 157
  (Polychromatic418967fa.accept_10_3_5_7_1_330 43 45 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 45 157 (Polychromatic418967fa.accept_10_2_5_7_1_1124 42 45 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 157 (accept_3_3 41 45 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 45 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 45 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 157 (Polychromatic418967fa.accept_12_3_9_1_1_290
  39 45 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 157 (accept_3_3 38
  45 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 157
  (Polychromatic418967fa.accept_21_16_3_10_1_6978 37 45 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 45 157 (Polychromatic418967fa.accept_19_17_7_5_1_1883 36 45 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 45 157 (accept_3_3 35 45 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 45 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 45 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 157 (Polychromatic418967fa.accept_10_3_5_7_1_330
  33 45 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 157 (accept_3_3 32
  45 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 157
  (Polychromatic418967fa.accept_13_5_6_1_1_822 31 45 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 45 157 (Polychromatic418967fa.accept_20_10_5_17_1_8556 30 45 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 45 157 (accept_3_3 29 45 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 45 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 45 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 157 (Polychromatic418967fa.accept_12_3_9_1_1_290
  27 45 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 157 (accept_3_3 26
  45 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 157
  (Polychromatic418967fa.accept_19_6_7_5_1_256 25 45 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 45 157 (Polychromatic418967fa.accept_11_2_1_3_1_683 24 45 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 45 157 (accept_3_3 23 45 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 45 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 45 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 157 (Polychromatic418967fa.accept_13_8_6_1_1_3808
  21 45 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 157 (accept_3_3 20
  45 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 157
  (Polychromatic418967fa.accept_25_19_20_7_1_8555 19 45 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 45 157 (Polychromatic418967fa.accept_10_8_5_7_1_358 18 45 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 157 (accept_3_3 17 45 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 45 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 45 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 157 (Polychromatic418967fa.accept_12_3_9_1_1_290
  15 45 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 157 (accept_3_3 14
  45 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 157
  (Polychromatic418967fa.accept_10_3_5_7_1_330 13 45 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 45 157 (Polychromatic418967fa.accept_10_2_5_7_1_1124 12 45 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 45 157 (accept_3_3 11 45 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 45 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 45 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 157 (Polychromatic418967fa.accept_13_9_6_1_1_2902 9
  45 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 157 (accept_3_3 8 45 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 157 (Polychromatic418967fa.accept_13_7_6_1_1_368 7
  45 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 157
  (Polychromatic418967fa.accept_17_6_11_4_1_1525 6 45 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 157 (accept_3_3 5 45 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45
  157 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 45 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 45 157 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 45 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 157 (accept_3_3 2 45 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 45 157 (Polychromatic418967fa.accept_21_1_3_10_1_5401 1 45 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 157))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  157 (allA_of_3_1 44 44 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 43 157 (allA_succ_of_accept 42 43 157
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 43 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 157 (accept_3_3 41 43 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 157 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 43 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 157 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 43 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 157 (accept_3_3 38 43 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 157 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 43 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 157
  (Polychromatic418967fa.accept_10_6_3_7_1_2197 36 43 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 157 (accept_3_3 35 43 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 43 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 157 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 43 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 157 (accept_3_3 32 43 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 157 (Polychromatic418967fa.accept_13_5_4_1_1_364 31 43 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 157
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 43 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 157 (accept_3_3 29 43 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 43 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 157 (Polychromatic418967fa.accept_23_4_20_19_1_8554 27 43 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 157 (accept_3_3 26 43 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 157 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 43 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 157
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 43 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 157 (accept_3_3 23 43 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 43 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 157 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 43 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 157 (accept_3_3 20 43 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 157 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 43 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 157
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 43 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 157 (accept_3_3 17 43 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 157 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 43 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 157 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 43 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 157 (accept_3_3 14 43 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 157 (Polychromatic418967fa.accept_17_13_9_4_1_5979 13 43 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 157
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 43 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 157 (accept_3_3 11 43 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 43 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 157 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 43 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 157 (accept_3_3 8 43 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 157 (Polychromatic418967fa.accept_11_7_10_3_1_633 7 43 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 157
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 43 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 157 (accept_3_3 5 43 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  157 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 43 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 157 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 43 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 157 (accept_3_3 2 43 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 43 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 157))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 157
  (allA_succ_of_accept 41 42 157 (accept_3_3 41 42 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  42 157 (Polychromatic418967fa.accept_15_10_12_7_1_1358 40 42 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 42 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 42 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 42 157 (accept_3_3 38 42 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 157 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 42 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 157
  (Polychromatic418967fa.accept_15_6_12_7_1_1360 36 42 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 42 157 (accept_3_3 35 42 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  42 157 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 42 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 42 157 (Polychromatic418967fa.accept_13_7_3_1_1_814 33 42 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 42 157 (accept_3_3 32 42 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 42 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 42 157
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 42 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 42 157 (accept_3_3 29 42 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  42 157 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 42 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 42 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 42 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 42 157 (accept_3_3 26 42 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 157 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 42 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 157
  (Polychromatic418967fa.accept_10_4_2_7_1_373 24 42 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 42 157 (accept_3_3 23 42 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  42 157 (Polychromatic418967fa.accept_29_22_13_12_1_8553 22 42 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 42 157 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 42 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 42 157 (accept_3_3 20 42 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 42 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 42 157
  (Polychromatic418967fa.accept_13_5_3_1_1_1398 18 42 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 42 157 (accept_3_3 17 42 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  42 157 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 42 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 42 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 42 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 42 157 (accept_3_3 14 42 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 157 (Polychromatic418967fa.accept_17_13_8_4_1_2514 13 42 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 157
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 42 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 42 157 (accept_3_3 11 42 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  42 157 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 42 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 42 157 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 42 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 42 157 (accept_3_3 8 42 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 42 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 42 157
  (Polychromatic418967fa.accept_11_6_9_3_1_1103 6 42 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 42 157 (accept_3_3 5 42 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42
  157 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 42 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 42 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 42 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 42 157 (accept_3_3 2 42 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 42 157 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 42 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42 157)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 157
  (allA_of_3_1 41 41 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 40 157 (allA_succ_of_accept 39 40 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 40 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 40 157 (accept_3_3 38 40 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  40 157 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 40 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 40 157 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 40 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 40 157 (accept_3_3 35 40 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 40 157 (Polychromatic418967fa.accept_12_10_4_1_1_1843 34 40 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 40 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 40 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 40 157 (accept_3_3 32 40 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  40 157 (Polychromatic418967fa.accept_15_1_10_7_1_4087 31 40 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 40 157 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 40 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 40 157 (accept_3_3 29 40 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 40 157 (Polychromatic418967fa.accept_16_12_8_13_1_6073 28 40 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 40 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 40 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 40 157 (accept_3_3 26 40 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  40 157 (Polychromatic418967fa.accept_18_7_4_13_1_3315 25 40 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 40 157 (Polychromatic418967fa.accept_26_24_14_1_1_8552 24 40 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 40 157 (accept_3_3 23 40 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 40 157 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 40 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 40 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 40 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 40 157 (accept_3_3 20 40 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  40 157 (Polychromatic418967fa.accept_14_5_12_3_1_3397 19 40 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 40 157 (Polychromatic418967fa.accept_15_3_10_7_1_2196 18 40 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 40 157 (accept_3_3 17 40 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 40 157 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 40 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 40 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 40 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 40 157 (accept_3_3 14 40 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  40 157 (Polychromatic418967fa.accept_23_13_17_19_1_8551 13 40 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 40 157 (Polychromatic418967fa.accept_15_12_10_7_1_1357 12 40 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 40 157 (accept_3_3 11 40 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 40 157 (Polychromatic418967fa.accept_11_10_7_3_1_3679 10 40
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 40 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 40 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 40 157 (accept_3_3 8 40 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 40
  157 (Polychromatic418967fa.accept_18_7_4_13_1_3315 7 40 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 40 157 (Polychromatic418967fa.accept_22_6_18_3_1_8550 6 40 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 40 157 (accept_3_3 5 40 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 40 157 (Polychromatic418967fa.accept_11_4_7_3_1_289 4 40 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 40 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 40 157 (accept_3_3 2 40 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40
  157 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 40 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 40 157)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 157 (allA_succ_of_accept 38 39 157 (accept_3_3
  38 39 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 157
  (Polychromatic418967fa.accept_9_1_3_4_1_47 37 39 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 39 157 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 39 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 39 157 (accept_3_3 35 39 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 39 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 39 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 157 (Polychromatic418967fa.accept_9_6_3_4_1_477 33
  39 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 157 (accept_3_3 32 39
  157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 157
  (Polychromatic418967fa.accept_11_9_6_3_1_1668 31 39 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 39 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 39 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 39 157 (accept_3_3 29 39 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 39 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 39 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 157 (Polychromatic418967fa.accept_7_6_4_3_1_266 27
  39 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 157 (accept_3_3 26 39
  157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 157
  (Polychromatic418967fa.accept_9_7_3_4_1_218 25 39 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 39 157 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 39 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 39 157 (accept_3_3 23 39 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 39 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 39 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 157 (Polychromatic418967fa.accept_12_9_3_1_1_303
  21 39 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 157 (accept_3_3 20
  39 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 157
  (Polychromatic418967fa.accept_9_1_3_4_1_47 19 39 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 39 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 39 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 39 157 (accept_3_3 17 39 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 39 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 39 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 157 (Polychromatic418967fa.accept_7_1_4_3_1_21 15
  39 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 157 (accept_3_3 14 39
  157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 157
  (Polychromatic418967fa.accept_7_6_4_3_1_266 13 39 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 39 157 (Polychromatic418967fa.accept_10_2_9_7_1_720 12 39 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 39 157 (accept_3_3 11 39 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 39 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 39 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 157 (Polychromatic418967fa.accept_11_9_6_3_1_1668 9
  39 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 157 (accept_3_3 8 39 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 157 (Polychromatic418967fa.accept_9_7_3_4_1_218 7
  39 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39 157
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 39 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 157 (accept_3_3 5 39 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39
  157 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 39 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 39 157 (Polychromatic418967fa.accept_19_3_1_5_1_8549 3 39 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 157 (accept_3_3 2 39 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 39 157 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 39 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 157))))))))))))))))))))))))))))))))))))))) (allB_succ 38 157
  (allA_of_3_1 38 38 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 37 157 (allA_succ_of_accept 36 37 157
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 37 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 37 157 (accept_3_3 35 37 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  37 157 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 37 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 37 157 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 37 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 157 (accept_3_3 32 37 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 157 (Polychromatic418967fa.accept_22_9_15_3_1_8548 31 37 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 157
  (Polychromatic418967fa.accept_9_3_1_4_1_216 30 37 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 157 (accept_3_3 29 37 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  37 157 (Polychromatic418967fa.accept_18_10_1_13_1_2192 28 37 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 157 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 37 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 157 (accept_3_3 26 37 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 157 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 37 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 157
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 37 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 157 (accept_3_3 23 37 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 157 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 37 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 157 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 37 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 157 (accept_3_3 20 37 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 157 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 37 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 157
  (Polychromatic418967fa.accept_11_7_4_3_1_302 18 37 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 157 (accept_3_3 17 37 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  37 157 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 37 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 157 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 37 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 157 (accept_3_3 14 37 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 157 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 37 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 157
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 37 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 157 (accept_3_3 11 37 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  37 157 (Polychromatic418967fa.accept_13_10_11_1_1_2152 10 37 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 157 (Polychromatic418967fa.accept_13_9_11_1_1_1375 9 37 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 157 (accept_3_3 8 37 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 157 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 37 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 157
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 37 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 157 (accept_3_3 5 37 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  157 (Polychromatic418967fa.accept_19_4_18_5_1_929 4 37 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 37 157 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 37 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 157 (accept_3_3 2 37 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 37 157 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 37 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 157))))))))))))))))))))))))))))))))))))) (allB_succ
  36 157 (allA_succ_of_accept 35 36 157 (accept_3_3 35 36 157 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 36 157 (Polychromatic418967fa.accept_19_15_17_5_1_3052 34 36 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 36 157 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 36 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 36 157 (accept_3_3 32 36 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 157 (Polychromatic418967fa.accept_10_1_6_7_1_710
  31 36 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 36 157
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 36 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 36 157 (accept_3_3 29 36 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  36 157 (Polychromatic418967fa.accept_15_13_6_7_1_1369 28 36 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 36 157 (Polychromatic418967fa.accept_15_12_6_7_1_1353 27 36 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 36 157 (accept_3_3 26 36 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 157 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 36 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 36 157
  (Polychromatic418967fa.accept_13_11_10_1_1_1409 24 36 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 36 157 (accept_3_3 23 36 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  36 157 (Polychromatic418967fa.accept_13_9_10_1_1_1389 22 36 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 36 157 (Polychromatic418967fa.accept_10_1_6_7_1_710 21 36 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 36 157 (accept_3_3 20 36 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 157 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 36 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 157
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 36 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 36 157 (accept_3_3 17 36 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  36 157 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 36 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 36 157 (Polychromatic418967fa.accept_17_15_2_4_1_2423 15 36 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 36 157 (accept_3_3 14 36 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 157 (Polychromatic418967fa.accept_10_3_6_7_1_2188 13 36 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 36 157
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 36 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 36 157 (accept_3_3 11 36 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  36 157 (Polychromatic418967fa.accept_23_10_13_19_1_8547 10 36 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 36 157 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 36 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 36 157 (accept_3_3 8 36 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 157 (Polychromatic418967fa.accept_16_7_4_13_1_1057 7 36 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 36 157
  (Polychromatic418967fa.accept_16_6_4_13_1_3841 6 36 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 36 157 (accept_3_3 5 36 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 36
  157 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 36 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 36 157 (Polychromatic418967fa.accept_10_3_6_7_1_2188 3 36 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 36 157 (accept_3_3 2 36 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 36 157 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 36 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 157)))))))))))))))))))))))))))))))))))) (allB_succ 35 157
  (allA_of_3_1 35 35 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 34 157 (allA_succ_of_accept 33 34 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 34 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 34 157 (accept_3_3 32 34 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  34 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 34 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 34 157 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 34 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 157 (accept_3_3 29 34 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 34 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 34 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 34 157
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 34 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 34 157 (accept_3_3 26 34 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  34 157 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 34 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 34 157 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 34 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 157 (accept_3_3 23 34 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 34 157 (Polychromatic418967fa.accept_10_2_4_7_1_352 22 34 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 34 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 34 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 34 157 (accept_3_3 20 34 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  34 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 34 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 34 157 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 34 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 34 157 (accept_3_3 17 34 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 34 157 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 34 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 34 157
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 34 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 34 157 (accept_3_3 14 34 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  34 157 (Polychromatic418967fa.accept_10_3_4_7_1_353 13 34 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 34 157 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 34 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 157 (accept_3_3 11 34 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 34 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 34 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 34 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 34 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 34 157 (accept_3_3 8 34 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 34
  157 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 34 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 34 157 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 34 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 157 (accept_3_3 5 34 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 34 157 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 34 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 34
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 34 157 (accept_3_3 2 34 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 34
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 157))))))))))))))))))))))))))))))))))
  (allB_succ 33 157 (allA_succ_of_accept 32 33 157 (accept_3_3 32 33 157 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 157 (Polychromatic418967fa.accept_22_9_11_3_1_5224 31 33 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 157 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 33 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 157 (accept_3_3 29 33 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 28
  33 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 157
  (Polychromatic418967fa.accept_12_3_9_1_1_290 27 33 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 33 157 (accept_3_3 26 33 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  33 157 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 33 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 33 157 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 33 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 157 (accept_3_3 23 33 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 33 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 157
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 33 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 33 157 (accept_3_3 20 33 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  33 157 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 33 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 33 157 (Polychromatic418967fa.accept_25_18_8_7_1_8546 18 33 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 157 (accept_3_3 17 33 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 33 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 157
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 33 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 33 157 (accept_3_3 14 33 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  33 157 (Polychromatic418967fa.accept_19_13_14_5_1_8545 13 33 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 33 157 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 33 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 157 (accept_3_3 11 33 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 33 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 157
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 33 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 33 157 (accept_3_3 8 33 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33
  157 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 33 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 33 157 (Polychromatic418967fa.accept_10_6_3_7_1_2197 6 33 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 157 (accept_3_3 5 33 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 33 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 33 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33 157 (Polychromatic418967fa.accept_9_3_6_4_1_210 3
  33 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 157 (accept_3_3 2 33 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 157 (Polychromatic418967fa.accept_7_1_5_3_1_268 1
  33 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 157)))))))))))))))))))))))))))))))))
  (allB_succ 32 157 (allA_of_3_1 32 32 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 31 157
  (allA_succ_of_accept 30 31 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 31 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 157 (accept_3_3 29 31 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 31 157 (Polychromatic418967fa.accept_11_6_9_3_1_1103 28 31 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 157 (Polychromatic418967fa.accept_19_8_12_5_1_7122
  27 31 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 157 (accept_3_3 26
  31 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 157
  (Polychromatic418967fa.accept_13_12_5_1_1_1383 25 31 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 31 157 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 31 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 157 (accept_3_3 23 31 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 31 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 31 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 157 (Polychromatic418967fa.accept_13_8_5_1_1_1381
  21 31 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 157 (accept_3_3 20
  31 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 157
  (Polychromatic418967fa.accept_13_6_5_1_1_834 19 31 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 31 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 31 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 31 157 (accept_3_3 17 31 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 31 157 (Polychromatic418967fa.accept_10_6_1_7_1_342 16 31 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 157
  (Polychromatic418967fa.accept_19_15_12_5_1_8544 15 31 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 31 157 (accept_3_3 14 31 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  31 157 (Polychromatic418967fa.accept_17_13_14_4_1_2468 13 31 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 31 157 (Polychromatic418967fa.accept_13_12_5_1_1_1383 12 31 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 31 157 (accept_3_3 11 31 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 31 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 31 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 31 157
  (Polychromatic418967fa.accept_13_9_5_1_1_1382 9 31 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 31 157 (accept_3_3 8 31 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 31
  157 (Polychromatic418967fa.accept_17_7_14_4_1_4745 7 31 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 31 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 31 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 31 157 (accept_3_3 5 31 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 31 157 (Polychromatic418967fa.accept_10_4_1_7_1_371 4 31 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 31 157
  (Polychromatic418967fa.accept_13_3_5_1_1_2144 3 31 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 31 157 (accept_3_3 2 31 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 31
  157 (Polychromatic418967fa.accept_17_1_14_4_1_1550 1 31 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 31 157))))))))))))))))))))))))))))))) (allB_succ 30 157 (allA_succ_of_accept 29 30 157
  (accept_3_3 29 30 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 30 157
  (Polychromatic418967fa.accept_9_1_3_4_1_47 28 30 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 30 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 30 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 30 157 (accept_3_3 26 30 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 30 157 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 30 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 30 157 (Polychromatic418967fa.accept_9_6_3_4_1_477 24
  30 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 30 157 (accept_3_3 23 30
  157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 30 157
  (Polychromatic418967fa.accept_7_1_2_3_1_257 22 30 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 30 157 (Polychromatic418967fa.accept_18_3_12_13_1_3307 21 30 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 30 157 (accept_3_3 20 30 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 30 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 30 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 157 (Polychromatic418967fa.accept_13_5_4_1_1_364
  18 30 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 30 157 (accept_3_3 17
  30 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 30 157
  (Polychromatic418967fa.accept_9_7_3_4_1_218 16 30 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 30 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 30 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 30 157 (accept_3_3 14 30 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 30 157 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 30 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 157 (Polychromatic418967fa.accept_7_5_2_3_1_106 12
  30 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 30 157 (accept_3_3 11 30
  157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 30 157 (Polychromatic418967fa.accept_9_1_3_4_1_47
  10 30 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 30 157
  (Polychromatic418967fa.accept_17_9_13_4_1_2408 9 30 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 30 157 (accept_3_3 8 30 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30
  157 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 30 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 30 157 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 30 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 30 157 (accept_3_3 5 30 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 30 157 (Polychromatic418967fa.accept_29_4_1_12_1_8543 4 30 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 30 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 30
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 30 157 (accept_3_3 2 30 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 157 (Polychromatic418967fa.accept_7_1_2_3_1_257 1
  30 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 157))))))))))))))))))))))))))))))
  (allB_succ 29 157 (allA_of_3_1 29 29 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 28 157
  (allA_succ_of_accept 27 28 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 28 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 28 157 (accept_3_3 26 28 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 28 157 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 28 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 28 157 (Polychromatic418967fa.accept_9_6_1_4_1_474 24
  28 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 157 (accept_3_3 23 28
  157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 28 157
  (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 28 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 28 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 28 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 28 157 (accept_3_3 20 28 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 28 157 (Polychromatic418967fa.accept_10_9_8_7_1_714 19 28 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 28 157 (Polychromatic418967fa.accept_19_18_9_5_1_8542
  18 28 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 28 157 (accept_3_3 17
  28 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 28 157
  (Polychromatic418967fa.accept_9_7_1_4_1_217 16 28 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 28 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 28 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 28 157 (accept_3_3 14 28 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 28 157 (Polychromatic418967fa.accept_19_13_9_5_1_8541 13 28 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 28 157
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 28 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 28 157 (accept_3_3 11 28 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  28 157 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 28 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 28 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 28 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 28 157 (accept_3_3 8 28 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 28 157 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 28 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 28 157
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 28 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 28 157 (accept_3_3 5 28 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 28
  157 (Polychromatic418967fa.accept_16_4_12_13_1_990 4 28 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 28 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 28 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 28 157 (accept_3_3 2 28 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 28 157 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 28 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 157)))))))))))))))))))))))))))) (allB_succ 27 157
  (allA_succ_of_accept 26 27 157 (accept_3_3 26 27 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  27 157 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 27 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 27 157 (Polychromatic418967fa.accept_14_10_13_3_1_2552 24 27 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 157 (accept_3_3 23 27 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 27 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 157
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 27 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 27 157 (accept_3_3 20 27 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  27 157 (Polychromatic418967fa.accept_11_8_5_3_1_694 19 27 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 27 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 27 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 157 (accept_3_3 17 27 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 27 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 157
  (Polychromatic418967fa.accept_17_15_10_4_1_8540 15 27 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 27 157 (accept_3_3 14 27 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  27 157 (Polychromatic418967fa.accept_19_13_8_5_1_8539 13 27 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 27 157 (Polychromatic418967fa.accept_19_12_8_5_1_8538 12 27 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 157 (accept_3_3 11 27 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 27 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 157
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 27 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 27 157 (accept_3_3 8 27 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27
  157 (Polychromatic418967fa.accept_28_7_27_17_1_8537 7 27 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 27 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 27 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 157 (accept_3_3 5 27 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 27 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 157
  (Polychromatic418967fa.accept_15_3_12_7_1_1346 3 27 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 27 157 (accept_3_3 2 27 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27
  157 (Polychromatic418967fa.accept_22_1_5_3_1_8536 1 27 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 27 157))))))))))))))))))))))))))) (allB_succ 26 157 (allA_of_3_1 26 26 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 25 157 (allA_succ_of_accept 24 25 157 (Polychromatic418967fa.accept_9_6_7_4_1_212 24
  25 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 157 (accept_3_3 23 25
  157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 25 157 (Polychromatic418967fa.accept_7_1_4_3_1_21
  22 25 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 157
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 25 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 25 157 (accept_3_3 20 25 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  25 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 25 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 25 157 (Polychromatic418967fa.accept_10_8_5_7_1_358 18 25 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 157 (accept_3_3 17 25 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 25 157 (Polychromatic418967fa.accept_15_1_10_7_1_4087 16 25 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 25 157
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 25 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 25 157 (accept_3_3 14 25 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  25 157 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 25 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 25 157 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 25 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 157 (accept_3_3 11 25 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 25 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 25 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 25 157
  (Polychromatic418967fa.accept_24_9_1_13_1_8535 9 25 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 25 157 (accept_3_3 8 25 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25
  157 (Polychromatic418967fa.accept_14_7_11_3_1_5365 7 25 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 25 157 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 25 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 25 157 (accept_3_3 5 25 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 25 157 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 25 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 157
  (Polychromatic418967fa.accept_9_3_7_4_1_53 3 25 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 25 157 (accept_3_3 2 25 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25
  157 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 25 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 25 157))))))))))))))))))))))))) (allB_succ 24 157 (allA_succ_of_accept 23 24 157 (accept_3_3 23 24 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 157 (Polychromatic418967fa.accept_10_2_4_7_1_352
  22 24 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 24 157
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 24 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 24 157 (accept_3_3 20 24 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  24 157 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 24 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 24 157 (Polychromatic418967fa.accept_21_18_3_10_1_8534 18 24 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 24 157 (accept_3_3 17 24 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 157 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 24 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 24 157
  (Polychromatic418967fa.accept_21_15_3_10_1_8533 15 24 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 24 157 (accept_3_3 14 24 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  24 157 (Polychromatic418967fa.accept_10_3_4_7_1_353 13 24 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 24 157 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 24 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 24 157 (accept_3_3 11 24 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 24 157 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 24 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 24 157
  (Polychromatic418967fa.accept_13_9_11_1_1_1375 9 24 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 24 157 (accept_3_3 8 24 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24
  157 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 24 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 24 157 (Polychromatic418967fa.accept_14_6_10_3_1_1038 6 24 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 24 157 (accept_3_3 5 24 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 24 157 (Polychromatic418967fa.accept_16_4_8_13_1_1059 4 24 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 24 157 (Polychromatic418967fa.accept_9_3_6_4_1_210 3
  24 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 24 157 (accept_3_3 2 24 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 24 157 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 24
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 157)))))))))))))))))))))))) (allB_succ
  23 157 (allA_of_3_1 23 23 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 22 157 (allA_succ_of_accept 21 22
  157 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 22 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 22 157 (accept_3_3 20 22 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  22 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 22 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 22 157 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 22 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 157 (accept_3_3 17 22 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 22 157 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 22 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 22 157
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 22 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 22 157 (accept_3_3 14 22 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  22 157 (Polychromatic418967fa.accept_21_13_1_10_1_5377 13 22 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 22 157 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 22 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 22 157 (accept_3_3 11 22 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 22 157 (Polychromatic418967fa.accept_13_10_9_1_1_5609 10 22 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 22 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 22 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 22 157 (accept_3_3 8 22 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 22
  157 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 22 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 22 157 (Polychromatic418967fa.accept_13_6_9_1_1_5604 6 22 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 157 (accept_3_3 5 22 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 22 157 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 22 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 22 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 22
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 22 157 (accept_3_3 2 22 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 22 157 (Polychromatic418967fa.accept_17_1_5_4_1_8532 1
  22 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 157)))))))))))))))))))))) (allB_succ
  21 157 (allA_succ_of_accept 20 21 157 (accept_3_3 20 21 157 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 157 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 21 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 157 (Polychromatic418967fa.accept_11_7_10_3_1_633 18 21 157
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 157 (accept_3_3 17 21 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 16
  21 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 157
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 21 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 21 157 (accept_3_3 14 21 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  21 157 (Polychromatic418967fa.accept_15_13_6_7_1_1369 13 21 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 21 157 (Polychromatic418967fa.accept_13_12_8_1_1_825 12 21 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 157 (accept_3_3 11 21 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 21 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 157
  (Polychromatic418967fa.accept_13_9_8_1_1_824 9 21 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 21 157 (accept_3_3 8 21 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21
  157 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 21 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 21 157 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 21 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 157 (accept_3_3 5 21 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 21 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 21 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21 157 (Polychromatic418967fa.accept_12_3_9_1_1_290 3
  21 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 157 (accept_3_3 2 21 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 157 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 21
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 157))))))))))))))))))))) (allB_succ 20
  157 (allA_of_3_1 20 20 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 19 157 (allA_succ_of_accept 18 19 157
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 19 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 157 (accept_3_3 17 19 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 157 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 19 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 157 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 19 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 157 (accept_3_3 14 19 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 157 (Polychromatic418967fa.accept_25_13_19_7_1_6688 13 19 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 157
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 19 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 157 (accept_3_3 11 19 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 19 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 157 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 19 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 157 (accept_3_3 8 19 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 157 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 19 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 157
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 19 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 157 (accept_3_3 5 19 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  157 (Polychromatic418967fa.accept_21_4_19_10_1_8531 4 19 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 19 157 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 19 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 157 (accept_3_3 2 19 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 19 157 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 19 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 157))))))))))))))))))) (allB_succ 18 157
  (allA_succ_of_accept 17 18 157 (accept_3_3 17 18 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  18 157 (Polychromatic418967fa.accept_13_3_5_1_1_2144 16 18 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 18 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 18 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 157 (accept_3_3 14 18 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 18 157 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 18 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 18 157
  (Polychromatic418967fa.accept_13_12_5_1_1_1383 12 18 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 18 157 (accept_3_3 11 18 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  18 157 (Polychromatic418967fa.accept_11_10_7_3_1_3679 10 18 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 18 157 (Polychromatic418967fa.accept_10_9_8_7_1_714 9 18 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 157 (accept_3_3 8 18 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 18 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 18 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18 157
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 18 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 18 157 (accept_3_3 5 18 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18
  157 (Polychromatic418967fa.accept_11_4_7_3_1_289 4 18 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 18 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 18 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 18 157 (accept_3_3 2 18 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 18 157 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 18 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 157)))))))))))))))))) (allB_succ 17 157 (allA_of_3_1 17 17 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 16 157 (allA_succ_of_accept 15 16 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 16 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 16 157 (accept_3_3 14 16 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  16 157 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 16 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 16 157 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 16 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 16 157 (accept_3_3 11 16 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 16 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 16 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 16 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 16 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 16 157 (accept_3_3 8 16 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 16
  157 (Polychromatic418967fa.accept_13_7_3_1_1_814 7 16 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 16 157 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 16 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 16 157 (accept_3_3 5 16 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 16 157 (Polychromatic418967fa.accept_13_4_3_1_1_2898 4 16 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 16 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 16
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 16 157 (accept_3_3 2 16 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 16 157 (Polychromatic418967fa.accept_7_1_2_3_1_257 1
  16 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 157)))))))))))))))) (allB_succ 15 157
  (allA_succ_of_accept 14 15 157 (accept_3_3 14 15 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  15 157 (Polychromatic418967fa.accept_10_3_5_7_1_330 13 15 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 15 157 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 15 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 157 (accept_3_3 11 15 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 15 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 157
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 15 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 15 157 (accept_3_3 8 15 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15
  157 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 15 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 15 157 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 15 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 15 157 (accept_3_3 5 15 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 15 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 15 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 15 157 (Polychromatic418967fa.accept_9_3_6_4_1_210 3
  15 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 157 (accept_3_3 2 15 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 157 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 15
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 157))))))))))))))) (allB_succ 14 157
  (allA_of_3_1 14 14 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 157 (allA_succ_of_accept 12 13 157
  (Polychromatic418967fa.accept_11_1_2_3_1_688 12 13 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 157 (accept_3_3 11 13 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 157 (Polychromatic418967fa.accept_14_10_13_3_1_2552 10 13 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 157 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 13 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 157 (accept_3_3 8 13 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 157 (Polychromatic418967fa.accept_19_7_13_5_1_7125 7 13 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 157
  (Polychromatic418967fa.accept_10_6_3_7_1_2197 6 13 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 157 (accept_3_3 5 13 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  157 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 13 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 157 (Polychromatic418967fa.accept_17_3_13_4_1_8530 3 13 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 157 (accept_3_3 2 13 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 157 (Polychromatic418967fa.accept_11_1_2_3_1_688 1 13 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 157))))))))))))) (allB_succ 12 157 (allA_succ_of_accept 11 12
  157 (accept_3_3 11 12 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 157
  (Polychromatic418967fa.accept_9_1_3_4_1_47 10 12 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 12 157 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 12 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 157 (accept_3_3 8 12 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 12 157 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 12 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12 157 (Polychromatic418967fa.accept_9_6_3_4_1_477 6
  12 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 12 157 (accept_3_3 5 12 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 157 (Polychromatic418967fa.accept_10_4_2_7_1_373 4
  12 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 12 157
  (Polychromatic418967fa.accept_15_3_12_7_1_1346 3 12 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 12 157 (accept_3_3 2 12 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12
  157 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 12 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 12 157)))))))))))) (allB_succ 11 157 (allA_of_3_1 11 11 157 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 10 157 (allA_succ_of_accept 9 10 157 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 10 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 10 157 (accept_3_3 8 10 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 10 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 10 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 10 157
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 10 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 10 157 (accept_3_3 5 10 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 10
  157 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 10 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 10 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 10 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 10 157 (accept_3_3 2 10 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 10 157 (Polychromatic418967fa.accept_15_1_10_7_1_4087 1 10 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 157)))))))))) (allB_succ 9 157 (allA_succ_of_accept 8
  9 157 (accept_3_3 8 9 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 157
  (Polychromatic418967fa.accept_16_7_9_13_1_4948 7 9 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 9 157 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 9 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 157 (accept_3_3 5 9 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 9 157 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 9 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 157 (Polychromatic418967fa.accept_12_3_9_1_1_290 3 9
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 157 (accept_3_3 2 9 157
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 157 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 9
  157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 157))))))))) (allB_succ 8 157
  (allA_of_3_1 8 8 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 7 157 (allA_succ_of_accept 6 7 157
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 7 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 157 (accept_3_3 5 7 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 157
  (Polychromatic418967fa.accept_11_4_7_3_1_289 4 7 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 157 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 7 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 157 (accept_3_3 2 7 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 157 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 7 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 157))))))) (allB_succ 6 157 (allA_succ_of_accept 5 6 157
  (accept_3_3 5 6 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 6 157
  (Polychromatic418967fa.accept_7_4_6_3_1_271 4 6 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 6 157 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 6 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 6 157 (accept_3_3 2 6 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 6 157 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 6 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 157)))))) (allB_succ 5 157 (allA_of_3_1 5 5 157 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 4 157 (allA_succ_of_accept 3 4 157
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 4 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 157 (accept_3_3 2 4 157 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 157
  (Polychromatic418967fa.accept_7_1_4_3_1_21 1 4 157 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 157)))) (allB_succ 3 157 (allA_succ_of_accept 2 3 157 (accept_3_3 2 3 157 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 157 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 3 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 157))) (allB_succ 2 157 (allA_of_3_1 2 2 157 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  157)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


