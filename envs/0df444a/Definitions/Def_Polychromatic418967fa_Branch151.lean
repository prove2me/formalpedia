-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch151
-- name    : Polychromatic418967fa_Branch151
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:16:12.989675+00:00
-- url     : https://prove2.me/theorems/aa14afcf-8654-4731-80a7-b1df6e0132f7
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

def Polychromatic418967fa.branch_151 : allB 151 151 :=
  allB_succ' 2 150 151 (Eq.refl Bool.true) (allA_succ_of_accept 1 150 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 1
  150 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150 151)) (allB_succ' 3 149 151
  (Eq.refl Bool.true) (allA_of_3_1 3 149 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 148 151 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 148 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 148 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 148 151 (accept_3_3 2 148 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 148 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 148 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 148 151)))) (allB_succ' 5 147 151 (Eq.refl Bool.true)
  (allA_succ_of_accept 4 147 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 147 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 147 151 (Polychromatic418967fa.accept_14_3_7_11_1_765 3 147 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 147 151 (accept_3_3 2 147 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 151 (Polychromatic418967fa.accept_9_1_3_7_1_6 1
  147 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 147 151))))) (allB_succ' 6 146 151
  (Eq.refl Bool.true) (allA_of_3_1 6 146 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 145 151 (Eq.refl
  Bool.true) (allA_succ_of_accept 6 145 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 145 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 145 151 (accept_3_3 5 145 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 145 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 145 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 145 151
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 145 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 145 151 (accept_3_3 2 145 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  145 151 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 145 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 145 151))))))) (allB_succ' 8 144 151 (Eq.refl Bool.true) (allA_succ_of_accept 7 144 151
  (Polychromatic418967fa.accept_10_7_4_1_1_1319 7 144 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 144 151 (Polychromatic418967fa.accept_13_6_1_8_1_1116 6 144 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 144 151 (accept_3_3 5 144 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 144 151 (Polychromatic418967fa.accept_11_4_1_8_1_1366 4 144 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 144 151
  (Polychromatic418967fa.accept_19_3_11_18_1_2709 3 144 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 144 151 (accept_3_3 2 144 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  144 151 (Polychromatic418967fa.accept_14_1_4_11_1_3036 1 144 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 144 151)))))))) (allB_succ' 9 143 151 (Eq.refl Bool.true) (allA_of_3_1 9 143 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 142 151 (Eq.refl Bool.true) (allA_succ_of_accept 9 142 151
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 142 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 142 151 (accept_3_3 8 142 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  142 151 (Polychromatic418967fa.accept_13_7_12_8_1_199 7 142 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 142 151 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 142 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 142 151 (accept_3_3 5 142 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 142 151 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 142 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 142 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 142 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 142 151 (accept_3_3 2 142 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  142 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 142 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 142 151)))))))))) (allB_succ' 11 141 151 (Eq.refl Bool.true) (allA_succ_of_accept 10 141 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 10 141 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 141 151 (Polychromatic418967fa.accept_13_9_11_8_1_195 9 141 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 141 151 (accept_3_3 8 141 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 141 151 (Polychromatic418967fa.accept_15_7_6_1_1_1091 7 141 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 141 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 6
  141 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 141 151 (accept_3_3 5 141
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 151 (Polychromatic418967fa.accept_6_4_3_1_1_57
  4 141 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 141 151
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 141 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 141 151 (accept_3_3 2 141 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  141 151 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 141 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 141 151))))))))))) (allB_succ' 12 140 151 (Eq.refl Bool.true) (allA_of_3_1 12 140 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 139 151 (Eq.refl Bool.true) (allA_succ_of_accept 12 139 151
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 139 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 139 151 (accept_3_3 11 139 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 139 151 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 139 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 139 151 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 139 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 139 151 (accept_3_3 8 139 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 139 151 (Polychromatic418967fa.accept_13_7_9_8_1_188 7 139 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 139 151
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 139 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 139 151 (accept_3_3 5 139 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  139 151 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 139 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 139 151 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 139 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 139 151 (accept_3_3 2 139 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 139 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 139 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 139 151))))))))))))) (allB_succ' 14 138 151 (Eq.refl
  Bool.true) (allA_succ_of_accept 13 138 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 138 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 138 151
  (Polychromatic418967fa.accept_22_12_6_19_1_8159 12 138 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 138 151 (accept_3_3 11 138 151 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 138 151 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 138 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 138 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 138 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 138 151 (accept_3_3 8 138 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 138 151 (Polychromatic418967fa.accept_17_7_2_15_1_1255
  7 138 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 138 151
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 138 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 138 151 (accept_3_3 5 138 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  138 151 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 138 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 138 151 (Polychromatic418967fa.accept_10_3_8_1_1_182 3 138 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 138 151 (accept_3_3 2 138 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 138 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 138 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138 151)))))))))))))) (allB_succ' 15 137 151 (Eq.refl
  Bool.true) (allA_of_3_1 15 137 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 136 151 (Eq.refl Bool.true)
  (allA_succ_of_accept 15 136 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 136 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 136 151 (accept_3_3 14 136 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 136 151 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 136 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 136 151 (Polychromatic418967fa.accept_9_3_1_7_1_97 12
  136 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 136 151 (accept_3_3 11
  136 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 136 151
  (Polychromatic418967fa.accept_12_10_4_7_1_948 10 136 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 136 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 136 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 136 151 (accept_3_3 8 136 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 136 151 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 136 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 136 151 (Polychromatic418967fa.accept_7_6_3_4_1_294 6
  136 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 136 151 (accept_3_3 5 136
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 136 151
  (Polychromatic418967fa.accept_9_4_1_7_1_293 4 136 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 136 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 136 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 136 151 (accept_3_3 2 136 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 136 151 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 136 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 136 151)))))))))))))))) (allB_succ' 17 135 151 (Eq.refl Bool.true)
  (allA_succ_of_accept 16 135 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 135 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 135 151 (Polychromatic418967fa.accept_19_15_2_18_1_6699 15 135
  151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 135 151 (accept_3_3 14 135
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 151
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 135 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 135 151 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 135 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 135 151 (accept_3_3 11 135 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 135 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 135 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 135 151 (Polychromatic418967fa.accept_10_9_5_1_1_1325
  9 135 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 135 151 (accept_3_3 8
  135 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 151
  (Polychromatic418967fa.accept_22_7_3_19_1_8158 7 135 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 135 151 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 135 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 135 151 (accept_3_3 5 135 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 135 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 135 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 135 151 (Polychromatic418967fa.accept_13_3_5_8_1_1099
  3 135 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 135 151 (accept_3_3 2
  135 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 151
  (Polychromatic418967fa.accept_13_1_5_8_1_207 1 135 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 135 151))))))))))))))))) (allB_succ' 18 134 151 (Eq.refl Bool.true) (allA_of_3_1 18 134 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 133 151 (Eq.refl Bool.true) (allA_succ_of_accept 18 133 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 133 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 133 151 (accept_3_3 17 133 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 133 151 (Polychromatic418967fa.accept_17_16_14_15_1_1250 16 133 151 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 133 151 (Polychromatic418967fa.accept_11_4_1_8_1_1366 15 133 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 133 151 (accept_3_3 14 133 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 133 151 (Polychromatic418967fa.accept_21_13_7_4_1_4991 13 133
  151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 133 151
  (Polychromatic418967fa.accept_10_2_3_1_1_481 12 133 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 133 151 (accept_3_3 11 133 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 133 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 133 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 133 151 (Polychromatic418967fa.accept_13_9_3_8_1_573 9 133 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 133 151 (accept_3_3 8 133 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 133 151 (Polychromatic418967fa.accept_13_7_3_8_1_1750 7 133 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 133 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 133 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 133 151 (accept_3_3 5 133 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  133 151 (Polychromatic418967fa.accept_11_4_1_8_1_1366 4 133 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 133 151 (Polychromatic418967fa.accept_14_3_7_11_1_765 3 133 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 133 151 (accept_3_3 2 133 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 133 151 (Polychromatic418967fa.accept_21_1_7_4_1_4947 1 133 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 133 151))))))))))))))))))) (allB_succ' 20 132 151
  (Eq.refl Bool.true) (allA_succ_of_accept 19 132 151 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 132 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 132 151
  (Polychromatic418967fa.accept_21_18_6_4_1_5031 18 132 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 132 151 (accept_3_3 17 132 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 132 151 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 132 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 132 151 (Polychromatic418967fa.accept_21_15_6_4_1_4990 15 132 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 132 151 (accept_3_3 14 132 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 132 151 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 132 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 132 151
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 132 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 132 151 (accept_3_3 11 132 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 132 151 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 132 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 132 151 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 132 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 132 151 (accept_3_3 8 132 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 132 151 (Polychromatic418967fa.accept_13_7_2_8_1_1746 7 132 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 132 151
  (Polychromatic418967fa.accept_10_6_2_1_1_494 6 132 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 132 151 (accept_3_3 5 132 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  132 151 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 132 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 132 151 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 132 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 132 151 (accept_3_3 2 132 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 132 151 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 132 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132 151)))))))))))))))))))) (allB_succ' 21 131 151
  (Eq.refl Bool.true) (allA_of_3_1 21 131 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 130 151 (Eq.refl
  Bool.true) (allA_succ_of_accept 21 130 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 130 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 130 151 (accept_3_3 20 130 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 130 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 130 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 130 151
  (Polychromatic418967fa.accept_24_18_10_7_1_8157 18 130 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 130 151 (accept_3_3 17 130 151 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 130 151 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 130 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 130 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 130 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 130 151 (accept_3_3 14 130 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 130 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 13
  130 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 130 151
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 130 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 130 151 (accept_3_3 11 130 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 130 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 130 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 130 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 130 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 130 151 (accept_3_3 8 130 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 130 151 (Polychromatic418967fa.accept_14_7_4_11_1_3038 7 130 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 130 151
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 130 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 130 151 (accept_3_3 5 130 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  130 151 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 130 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 130 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 130 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 130 151 (accept_3_3 2 130 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 130 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 130 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 130 151)))))))))))))))))))))) (allB_succ' 23 129 151
  (Eq.refl Bool.true) (allA_succ_of_accept 22 129 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 129 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 129 151
  (Polychromatic418967fa.accept_14_7_3_11_1_2199 21 129 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 129 151 (accept_3_3 20 129 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 129 151 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 129 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 129 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 129 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 129 151 (accept_3_3 17 129 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 129 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 129 151
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 129 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 129 151 (accept_3_3 14 129 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 129 151 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 129 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 129 151 (Polychromatic418967fa.accept_10_2_9_1_1_185 12 129 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 129 151 (accept_3_3 11 129 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 129 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 129 151
  (Polychromatic418967fa.accept_13_9_12_8_1_570 9 129 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 129 151 (accept_3_3 8 129 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  129 151 (Polychromatic418967fa.accept_13_7_12_8_1_199 7 129 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 129 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 129 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 129 151 (accept_3_3 5 129 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 129 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 129 151
  (Polychromatic418967fa.accept_12_3_9_7_1_472 3 129 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 129 151 (accept_3_3 2 129 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  129 151 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 129 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 129 151))))))))))))))))))))))) (allB_succ' 24 128 151 (Eq.refl Bool.true) (allA_of_3_1 24 128
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 127 151 (Eq.refl Bool.true) (allA_succ_of_accept 24 127
  151 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 127 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 127 151 (accept_3_3 23 127 151 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 127 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 127 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 127 151 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 127 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 127 151 (accept_3_3 20 127 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 127 151 (Polychromatic418967fa.accept_7_5_1_4_1_122
  19 127 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 127 151
  (Polychromatic418967fa.accept_13_5_10_8_1_1127 18 127 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 127 151 (accept_3_3 17 127 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 127 151 (Polychromatic418967fa.accept_10_6_7_1_1_1297 16 127 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 127 151 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 127 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 127 151 (accept_3_3 14 127 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 127 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 127 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 127 151
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 127 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 127 151 (accept_3_3 11 127 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 127 151 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 127 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 127 151 (Polychromatic418967fa.accept_15_9_7_1_1_1075 9 127 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 127 151 (accept_3_3 8 127 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 127 151 (Polychromatic418967fa.accept_13_7_10_8_1_567 7 127 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 127 151
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 127 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 127 151 (accept_3_3 5 127 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  127 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 127 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 127 151 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 127 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 127 151 (accept_3_3 2 127 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 127 151 (Polychromatic418967fa.accept_19_1_13_18_1_6700 1 127 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 127 151))))))))))))))))))))))))) (allB_succ' 26 126 151
  (Eq.refl Bool.true) (allA_succ_of_accept 25 126 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 126 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 126 151
  (Polychromatic418967fa.accept_11_2_5_8_1_470 24 126 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 126 151 (accept_3_3 23 126 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 126 151 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 126 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 126 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 126 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 126 151 (accept_3_3 20 126 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 126 151 (Polychromatic418967fa.accept_17_2_7_15_1_5525 19 126 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 126 151
  (Polychromatic418967fa.accept_15_3_6_1_1_1834 18 126 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 126 151 (accept_3_3 17 126 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 126 151 (Polychromatic418967fa.accept_13_3_9_8_1_4202 16 126 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 126 151 (Polychromatic418967fa.accept_10_5_6_1_1_836 15 126 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 126 151 (accept_3_3 14 126 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 126 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 126 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 126 151
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 126 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 126 151 (accept_3_3 11 126 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 126 151 (Polychromatic418967fa.accept_15_10_6_1_1_3707 10 126 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 126 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 126 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 126 151 (accept_3_3 8 126 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 126 151 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 126 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 126 151
  (Polychromatic418967fa.accept_19_6_12_18_1_8141 6 126 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 126 151 (accept_3_3 5 126 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  126 151 (Polychromatic418967fa.accept_13_4_9_8_1_1736 4 126 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 126 151 (Polychromatic418967fa.accept_11_3_5_8_1_458 3 126 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 126 151 (accept_3_3 2 126 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 126 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 126 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126 151)))))))))))))))))))))))))) (allB_succ' 27 125 151
  (Eq.refl Bool.true) (allA_of_3_1 27 125 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 124 151 (Eq.refl
  Bool.true) (allA_succ_of_accept 27 124 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 124 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 124 151 (accept_3_3 26 124 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 124 151 (Polychromatic418967fa.accept_10_5_4_1_1_842 25 124 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 124 151
  (Polychromatic418967fa.accept_16_8_12_7_1_2399 24 124 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 124 151 (accept_3_3 23 124 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 124 151 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 124 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 124 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 124 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 124 151 (accept_3_3 20 124 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 124 151 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 124 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 124 151
  (Polychromatic418967fa.accept_15_3_4_1_1_1072 18 124 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 124 151 (accept_3_3 17 124 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 124 151 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 124 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 124 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 124 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 124 151 (accept_3_3 14 124 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 124 151 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 124 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 124 151
  (Polychromatic418967fa.accept_13_12_7_8_1_1104 12 124 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 124 151 (accept_3_3 11 124 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 124 151 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 124 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 124 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 124 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 124 151 (accept_3_3 8 124 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 124 151 (Polychromatic418967fa.accept_10_7_4_1_1_1319 7 124 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 124 151
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 124 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 124 151 (accept_3_3 5 124 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  124 151 (Polychromatic418967fa.accept_16_4_12_7_1_4475 4 124 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 124 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 124 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 124 151 (accept_3_3 2 124 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 124 151 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 124 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 124 151)))))))))))))))))))))))))))) (allB_succ' 29 123
  151 (Eq.refl Bool.true) (allA_succ_of_accept 28 123 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 123 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 123 151
  (Polychromatic418967fa.accept_11_5_2_8_1_866 27 123 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 123 151 (accept_3_3 26 123 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 123 151 (Polychromatic418967fa.accept_19_6_9_18_1_8140 25 123 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 123 151 (Polychromatic418967fa.accept_13_11_6_8_1_1121 24 123 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 123 151 (accept_3_3 23 123 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 123 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 123 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 123 151
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 123 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 123 151 (accept_3_3 20 123 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 123 151 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 123 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 123 151 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 123 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 123 151 (accept_3_3 17 123 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 123 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 123 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 123 151
  (Polychromatic418967fa.accept_13_2_6_8_1_1092 15 123 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 123 151 (accept_3_3 14 123 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 123 151 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 123 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 123 151 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 123 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 123 151 (accept_3_3 11 123 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 123 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 123 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 123 151
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 123 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 123 151 (accept_3_3 8 123 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  123 151 (Polychromatic418967fa.accept_21_7_18_4_1_5024 7 123 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 123 151 (Polychromatic418967fa.accept_15_6_3_1_1_3678 6 123 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 123 151 (accept_3_3 5 123 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 123 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 123 151
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 123 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 123 151 (accept_3_3 2 123 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  123 151 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 123 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 123 151))))))))))))))))))))))))))))) (allB_succ' 30 122 151 (Eq.refl Bool.true) (allA_of_3_1 30
  122 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 121 151 (Eq.refl Bool.true) (allA_succ_of_accept 30
  121 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 121 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 121 151 (accept_3_3 29 121 151 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 121 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 121 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 121 151 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 121 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 121 151 (accept_3_3 26 121 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 121 151
  (Polychromatic418967fa.accept_13_12_4_8_1_1120 25 121 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 121 151 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 121 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 121 151 (accept_3_3 23 121 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 121 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 121 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 121 151 (Polychromatic418967fa.accept_9_3_4_7_1_89 21
  121 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 121 151 (accept_3_3 20
  121 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 121 151
  (Polychromatic418967fa.accept_7_5_2_4_1_126 19 121 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 121 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 121 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 121 151 (accept_3_3 17 121 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 121 151 (Polychromatic418967fa.accept_14_2_9_11_1_3054 16 121 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 121 151
  (Polychromatic418967fa.accept_9_6_4_7_1_300 15 121 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 121 151 (accept_3_3 14 121 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 121 151 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 121 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 121 151 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 121 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 121 151 (accept_3_3 11 121 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 121 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 121 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 121 151
  (Polychromatic418967fa.accept_13_9_4_8_1_1752 9 121 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 121 151 (accept_3_3 8 121 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  121 151 (Polychromatic418967fa.accept_17_7_2_15_1_1255 7 121 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 121 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 121 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 121 151 (accept_3_3 5 121 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 121 151 (Polychromatic418967fa.accept_17_4_2_15_1_1254 4 121 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 121 151
  (Polychromatic418967fa.accept_9_3_4_7_1_89 3 121 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 121 151 (accept_3_3 2 121 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  121 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 121 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 121 151))))))))))))))))))))))))))))))) (allB_succ' 32 120 151 (Eq.refl Bool.true)
  (allA_succ_of_accept 31 120 151 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 120 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 120 151 (Polychromatic418967fa.accept_19_11_6_18_1_2717 30 120
  151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 120 151 (accept_3_3 29 120
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 120 151 (Polychromatic418967fa.accept_9_1_3_7_1_6
  28 120 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 120 151
  (Polychromatic418967fa.accept_21_6_15_4_1_5021 27 120 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 120 151 (accept_3_3 26 120 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 120 151 (Polychromatic418967fa.accept_16_9_8_7_1_4529 25 120 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 120 151 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 120 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 120 151 (accept_3_3 23 120 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 120 151 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 120 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 120 151
  (Polychromatic418967fa.accept_18_3_12_7_1_6728 21 120 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 120 151 (accept_3_3 20 120 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 120 151 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 120 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 120 151 (Polychromatic418967fa.accept_13_5_3_8_1_1117 18 120 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 120 151 (accept_3_3 17 120 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 120 151 (Polychromatic418967fa.accept_17_16_1_15_1_5541 16 120
  151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 120 151
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 120 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 120 151 (accept_3_3 14 120 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 120 151 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 120 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 120 151 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 120 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 120 151 (accept_3_3 11 120 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 120 151 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 120 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 120 151
  (Polychromatic418967fa.accept_11_9_10_8_1_444 9 120 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 120 151 (accept_3_3 8 120 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  120 151 (Polychromatic418967fa.accept_13_7_3_8_1_1750 7 120 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 120 151 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 120 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 120 151 (accept_3_3 5 120 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 120 151 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 120 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 120 151
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 120 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 120 151 (accept_3_3 2 120 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  120 151 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 120 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 120 151)))))))))))))))))))))))))))))))) (allB_succ' 33 119 151 (Eq.refl Bool.true) (allA_of_3_1
  33 119 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 118 151 (Eq.refl Bool.true) (allA_succ_of_accept 33
  118 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 118 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 118 151 (accept_3_3 32 118 151 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 118 151 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 118 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 118 151 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 118 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 118 151 (accept_3_3 29 118 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 118 151 (Polychromatic418967fa.accept_12_4_10_7_1_149
  28 118 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 118 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 118 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 118 151 (accept_3_3 26 118 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 118 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 118 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 118 151 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 118 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 118 151 (accept_3_3 23 118 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 118 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 118 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 118 151
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 118 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 118 151 (accept_3_3 20 118 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 118 151 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 118 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 118 151 (Polychromatic418967fa.accept_13_5_1_8_1_1115 18 118 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 118 151 (accept_3_3 17 118 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 118 151 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 118 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 118 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 118 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 118 151 (accept_3_3 14 118 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 118 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 118 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 118 151 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 118 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 118 151 (accept_3_3 11 118 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 118 151 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 118 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 118 151
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 118 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 118 151 (accept_3_3 8 118 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  118 151 (Polychromatic418967fa.accept_13_7_1_8_1_1778 7 118 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 118 151 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 118 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 118 151 (accept_3_3 5 118 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 118 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 118 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 118 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 118 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 118 151 (accept_3_3 2 118 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  118 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 118 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 118 151)))))))))))))))))))))))))))))))))) (allB_succ' 35 117 151 (Eq.refl Bool.true)
  (allA_succ_of_accept 34 117 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 117 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 117 151 (Polychromatic418967fa.accept_19_14_3_18_1_6675 33 117
  151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 117 151 (accept_3_3 32 117
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 151
  (Polychromatic418967fa.accept_26_5_13_21_1_6091 31 117 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 117 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 117 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 117 151 (accept_3_3 29 117 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 117 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 117 151
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 117 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 117 151 (accept_3_3 26 117 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 117 151 (Polychromatic418967fa.accept_19_6_3_18_1_5262 25 117 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 117 151 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 117 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 117 151 (accept_3_3 23 117 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 117 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 117 151
  (Polychromatic418967fa.accept_18_3_9_7_1_1839 21 117 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 117 151 (accept_3_3 20 117 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 117 151 (Polychromatic418967fa.accept_15_4_12_1_1_1081 19 117 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 117 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 117 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 117 151 (accept_3_3 17 117 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 117 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 117 151
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 117 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 117 151 (accept_3_3 14 117 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 117 151 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 117 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 117 151 (Polychromatic418967fa.accept_16_12_5_7_1_2360 12 117 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 117 151 (accept_3_3 11 117 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 117 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 151
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 117 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 117 151 (accept_3_3 8 117 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  117 151 (Polychromatic418967fa.accept_21_7_12_4_1_6493 7 117 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 117 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 117 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 117 151 (accept_3_3 5 117 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 117 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 117 151
  (Polychromatic418967fa.accept_12_3_9_7_1_472 3 117 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 117 151 (accept_3_3 2 117 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  117 151 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 117 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 117 151))))))))))))))))))))))))))))))))))) (allB_succ' 36 116 151 (Eq.refl Bool.true)
  (allA_of_3_1 36 116 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 115 151 (Eq.refl Bool.true)
  (allA_succ_of_accept 36 115 151 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 115 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 115 151 (accept_3_3 35 115 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 115 151 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 115 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 115 151
  (Polychromatic418967fa.accept_19_14_1_18_1_5280 33 115 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 115 151 (accept_3_3 32 115 151 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 115 151 (Polychromatic418967fa.accept_16_15_3_7_1_3389 31 115 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 115 151 (Polychromatic418967fa.accept_13_4_11_8_1_1768 30 115
  151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 115 151 (accept_3_3 29 115
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 115 151
  (Polychromatic418967fa.accept_8_4_3_7_1_491 28 115 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 115 151 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 115 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 115 151 (accept_3_3 26 115 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 115 151 (Polychromatic418967fa.accept_11_3_5_8_1_458 25 115 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 115 151
  (Polychromatic418967fa.accept_10_4_5_1_1_497 24 115 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 115 151 (accept_3_3 23 115 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 115 151 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 115 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 115 151 (Polychromatic418967fa.accept_14_7_3_11_1_2199 21 115 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 115 151 (accept_3_3 20 115 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 115 151 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 115
  151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 115 151
  (Polychromatic418967fa.accept_27_18_7_16_1_8156 18 115 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 115 151 (accept_3_3 17 115 151 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 115 151 (Polychromatic418967fa.accept_10_6_5_1_1_482 16 115 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 115 151 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 115 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 115 151 (accept_3_3 14 115 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 115 151 (Polychromatic418967fa.accept_7_6_3_4_1_294
  13 115 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 115 151
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 115 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 115 151 (accept_3_3 11 115 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 115 151 (Polychromatic418967fa.accept_13_10_11_8_1_1770 10 115 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 115 151 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 115 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 115 151 (accept_3_3 8 115 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 115 151 (Polychromatic418967fa.accept_14_7_3_11_1_2199 7 115 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 115 151
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 115 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 115 151 (accept_3_3 5 115 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  115 151 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 115 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 115 151 (Polychromatic418967fa.accept_11_3_5_8_1_458 3 115 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 151 (accept_3_3 2 115 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 115 151 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 115 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115 151))))))))))))))))))))))))))))))))))))) (allB_succ'
  38 114 151 (Eq.refl Bool.true) (allA_succ_of_accept 37 114 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 114 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 114 151
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 36 114 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 114 151 (accept_3_3 35 114 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 114 151 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 114 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 114 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 114 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 114 151 (accept_3_3 32 114 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 114 151 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 114 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 114 151
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 114 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 114 151 (accept_3_3 29 114 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 114 151 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 114 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 114 151 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 114 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 114 151 (accept_3_3 26 114 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 114 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 114 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 114 151
  (Polychromatic418967fa.accept_13_11_10_8_1_1804 24 114 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 114 151 (accept_3_3 23 114 151 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 114 151 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 114 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 114 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 114 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 114 151 (accept_3_3 20 114 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 114 151 (Polychromatic418967fa.accept_7_5_2_4_1_126
  19 114 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 114 151
  (Polychromatic418967fa.accept_11_7_4_8_1_1371 18 114 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 114 151 (accept_3_3 17 114 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 114 151 (Polychromatic418967fa.accept_21_16_9_4_1_8098 16 114 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 114 151 (Polychromatic418967fa.accept_10_5_4_1_1_842 15 114 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 114 151 (accept_3_3 14 114 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 114 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 114 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 114 151
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 114 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 114 151 (accept_3_3 11 114 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 114 151 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 114 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 114 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 114 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 114 151 (accept_3_3 8 114 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 114 151 (Polychromatic418967fa.accept_10_7_4_1_1_1319 7 114 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 114 151
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 114 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 114 151 (accept_3_3 5 114 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  114 151 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 114 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 114 151 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 114 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 114 151 (accept_3_3 2 114 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 114 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 114 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114 151))))))))))))))))))))))))))))))))))))))
  (allB_succ' 39 113 151 (Eq.refl Bool.true) (allA_of_3_1 39 113 151 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 40 112 151 (Eq.refl Bool.true) (allA_succ_of_accept 39 112 151 (Polychromatic418967fa.accept_6_3_4_1_1_8
  39 112 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 112 151 (accept_3_3 38
  112 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 112 151
  (Polychromatic418967fa.accept_9_1_4_7_1_7 37 112 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 112 151 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 112 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 112 151 (accept_3_3 35 112 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 112 151 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 112 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 112 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 112 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 112 151 (accept_3_3 32 112 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 112 151 (Polychromatic418967fa.accept_18_13_4_7_1_4086 31 112 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 112 151 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 112 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 112 151 (accept_3_3 29 112 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 112 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 112 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 112 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 112 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 112 151 (accept_3_3 26 112 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 112 151 (Polychromatic418967fa.accept_15_10_7_1_1_3686 25 112 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 112 151 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 112 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 112 151 (accept_3_3 23 112 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 112 151 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 112 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 112 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 112 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 112 151 (accept_3_3 20 112 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 112 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 112 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 112 151 (Polychromatic418967fa.accept_21_18_7_4_1_8131 18 112 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 112 151 (accept_3_3 17 112 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 112 151 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 112
  151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 112 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 112 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 112 151 (accept_3_3 14 112 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 112 151 (Polychromatic418967fa.accept_10_3_2_1_1_839 13 112 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 112 151 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 112 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 112 151 (accept_3_3 11 112 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 112 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 112 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 112 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 112 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 112 151 (accept_3_3 8 112 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  112 151 (Polychromatic418967fa.accept_19_7_17_18_1_8155 7 112 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 112 151 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 112 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 112 151 (accept_3_3 5 112 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 112 151 (Polychromatic418967fa.accept_17_4_10_15_1_5444 4 112 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 112 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 112 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 112 151 (accept_3_3 2 112 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  112 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 112 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 112 151)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 111 151 (Eq.refl Bool.true)
  (allA_succ_of_accept 40 111 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 111 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 111 151 (Polychromatic418967fa.accept_15_9_6_1_1_493 39 111
  151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 111 151 (accept_3_3 38 111
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 151
  (Polychromatic418967fa.accept_7_2_6_4_1_29 37 111 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 111 151 (Polychromatic418967fa.accept_13_10_7_8_1_1794 36 111 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 111 151 (accept_3_3 35 111 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 111 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 111 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 111 151 (Polychromatic418967fa.accept_7_5_6_4_1_117
  33 111 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 111 151 (accept_3_3 32
  111 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 151
  (Polychromatic418967fa.accept_7_3_6_4_1_30 31 111 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 111 151 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 111 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 111 151 (accept_3_3 29 111 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 111 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 111 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 111 151 (Polychromatic418967fa.accept_13_1_7_8_1_1796
  27 111 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 111 151 (accept_3_3 26
  111 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 151
  (Polychromatic418967fa.accept_13_12_7_8_1_1104 25 111 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 111 151 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 111 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 111 151 (accept_3_3 23 111 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 111 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 111 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 111 151 (Polychromatic418967fa.accept_12_9_3_7_1_924
  21 111 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 111 151 (accept_3_3 20
  111 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 151
  (Polychromatic418967fa.accept_7_5_6_4_1_117 19 111 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 111 151 (Polychromatic418967fa.accept_15_3_6_1_1_1834 18 111 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 151 (accept_3_3 17 111 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 111 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 111 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 111 151 (Polychromatic418967fa.accept_9_6_3_7_1_580
  15 111 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 111 151 (accept_3_3 14
  111 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 151
  (Polychromatic418967fa.accept_9_4_3_7_1_296 13 111 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 111 151 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 111 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 151 (accept_3_3 11 111 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 111 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 111 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 111 151 (Polychromatic418967fa.accept_7_2_6_4_1_29 9
  111 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 151 (accept_3_3 8 111
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 151
  (Polychromatic418967fa.accept_15_7_6_1_1_1091 7 111 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 111 151 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 111 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 151 (accept_3_3 5 111 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 111 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 111 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 111 151 (Polychromatic418967fa.accept_7_3_6_4_1_30 3
  111 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 151 (accept_3_3 2 111
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 151 (Polychromatic418967fa.accept_9_1_3_7_1_6
  1 111 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111
  151))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 110 151 (Eq.refl Bool.true) (allA_of_3_1 42 110 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 109 151 (Eq.refl Bool.true) (allA_succ_of_accept 42 109 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 109 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 109 151 (accept_3_3 41 109 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 109 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 109 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 109 151 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 109 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 109 151 (accept_3_3 38 109 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 109 151 (Polychromatic418967fa.accept_25_12_9_1_1_8154 37 109 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 109 151
  (Polychromatic418967fa.accept_13_10_5_8_1_2555 36 109 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 109 151 (accept_3_3 35 109 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 109 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 109 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 109 151 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 109 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 109 151 (accept_3_3 32 109 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 109 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 109 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 109 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 109 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 109 151 (accept_3_3 29 109 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 109 151 (Polychromatic418967fa.accept_10_8_9_1_1_189 28 109 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 109 151 (Polychromatic418967fa.accept_13_1_5_8_1_207 27 109 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 109 151 (accept_3_3 26 109 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 109 151 (Polychromatic418967fa.accept_10_5_9_1_1_187 25 109
  151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 109 151
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 109 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 109 151 (accept_3_3 23 109 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 109 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 109 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 109 151 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 109 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 109 151 (accept_3_3 20 109 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 109 151 (Polychromatic418967fa.accept_17_2_7_15_1_5525 19 109 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 109 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 109 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 109 151 (accept_3_3 17 109 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 109 151 (Polychromatic418967fa.accept_13_3_5_8_1_1099 16 109 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 109 151 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 109 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 109 151 (accept_3_3 14 109 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 109 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 109 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 109 151
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 109 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 109 151 (accept_3_3 11 109 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 109 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 109 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 109 151 (Polychromatic418967fa.accept_11_9_10_8_1_444 9 109 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 109 151 (accept_3_3 8 109 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 109 151 (Polychromatic418967fa.accept_19_7_14_18_1_6654 7 109 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 109 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 109 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 109 151 (accept_3_3 5 109 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  109 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 109 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 109 151 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 109 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 109 151 (accept_3_3 2 109 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 109 151 (Polychromatic418967fa.accept_13_1_5_8_1_207 1 109 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 109 151)))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 44 108 151 (Eq.refl Bool.true) (allA_succ_of_accept 43 108 151 (Polychromatic418967fa.accept_7_1_3_4_1_128
  43 108 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 108 151
  (Polychromatic418967fa.accept_17_8_6_15_1_523 42 108 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 108 151 (accept_3_3 41 108 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 108 151 (Polychromatic418967fa.accept_16_8_12_7_1_2399 40 108 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 108 151 (Polychromatic418967fa.accept_10_9_8_1_1_1331 39 108 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 108 151 (accept_3_3 38 108 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 108 151 (Polychromatic418967fa.accept_13_11_4_8_1_1098 37 108
  151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 108 151
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 108 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 108 151 (accept_3_3 35 108 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 108 151 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 108 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 108 151 (Polychromatic418967fa.accept_10_3_8_1_1_182 33 108 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 108 151 (accept_3_3 32 108 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 108 151 (Polychromatic418967fa.accept_17_14_6_15_1_3151 31 108
  151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 108 151
  (Polychromatic418967fa.accept_22_8_20_19_1_8153 30 108 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 108 151 (accept_3_3 29 108 151 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 108 151 (Polychromatic418967fa.accept_15_13_3_1_1_3740 28 108 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 108 151 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 108 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 108 151 (accept_3_3 26 108 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 108 151
  (Polychromatic418967fa.accept_13_12_4_8_1_1120 25 108 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 108 151 (Polychromatic418967fa.accept_13_11_4_8_1_1098 24 108 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 108 151 (accept_3_3 23 108 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 108 151 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 108 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 108 151
  (Polychromatic418967fa.accept_11_10_9_8_1_1974 21 108 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 108 151 (accept_3_3 20 108 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 108 151 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 108 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 108 151 (Polychromatic418967fa.accept_16_2_12_7_1_3410 18 108 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 108 151 (accept_3_3 17 108 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 108 151 (Polychromatic418967fa.accept_19_16_13_18_1_8152 16
  108 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 108 151
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 108 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 108 151 (accept_3_3 14 108 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 108 151 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 108 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 108 151 (Polychromatic418967fa.accept_13_12_4_8_1_1120 12 108 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 108 151 (accept_3_3 11 108 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 108 151 (Polychromatic418967fa.accept_11_10_9_8_1_1974 10 108
  151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 108 151
  (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 108 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 108 151 (accept_3_3 8 108 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  108 151 (Polychromatic418967fa.accept_14_7_10_11_1_8112 7 108 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 108 151 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 108 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 108 151 (accept_3_3 5 108 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 108 151 (Polychromatic418967fa.accept_15_4_3_1_1_487 4 108 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 108 151
  (Polychromatic418967fa.accept_8_3_4_7_1_475 3 108 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 108 151 (accept_3_3 2 108 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  108 151 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 108 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 108 151)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 107 151 (Eq.refl Bool.true)
  (allA_of_3_1 45 107 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 46 106 151 (Eq.refl Bool.true)
  (allA_succ_of_accept 45 106 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 106 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 106 151 (accept_3_3 44 106 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 106 151 (Polychromatic418967fa.accept_22_21_18_19_1_8151 43 106 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 106 151
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 106 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 106 151 (accept_3_3 41 106 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 106 151 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 106 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 106 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 106 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 106 151 (accept_3_3 38 106 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 106 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 106 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 106 151
  (Polychromatic418967fa.accept_13_10_2_8_1_2603 36 106 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 106 151 (accept_3_3 35 106 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 106 151 (Polychromatic418967fa.accept_20_14_6_11_1_6600 34 106 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 106 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 106 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 106 151 (accept_3_3 32 106 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 106 151 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 106 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 106 151
  (Polychromatic418967fa.accept_16_14_10_7_1_2363 30 106 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 106 151 (accept_3_3 29 106 151 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 106 151 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 106 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 106 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 106 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 106 151 (accept_3_3 26 106 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 106 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 25
  106 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 106 151
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 106 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 106 151 (accept_3_3 23 106 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 106 151 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 106 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 106 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 106 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 106 151 (accept_3_3 20 106 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 106 151 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 106 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 106 151
  (Polychromatic418967fa.accept_14_4_8_11_1_794 18 106 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 106 151 (accept_3_3 17 106 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 106 151 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 106 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 106 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 106 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 106 151 (accept_3_3 14 106 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 106 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 106 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 106 151
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 106 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 106 151 (accept_3_3 11 106 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 106 151 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 106 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 106 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 106 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 106 151 (accept_3_3 8 106 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 106 151 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 106 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 106 151
  (Polychromatic418967fa.accept_13_6_2_8_1_1782 6 106 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 106 151 (accept_3_3 5 106 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  106 151 (Polychromatic418967fa.accept_11_4_7_8_1_1926 4 106 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 106 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 106 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 106 151 (accept_3_3 2 106 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 106 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 106 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106 151))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 47 105 151 (Eq.refl Bool.true) (allA_succ_of_accept 46 105 151 (Polychromatic418967fa.accept_4_2_1_3_1_27
  46 105 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 105 151
  (Polychromatic418967fa.accept_13_6_1_8_1_1116 45 105 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 105 151 (accept_3_3 44 105 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 105 151 (Polychromatic418967fa.accept_19_5_10_18_1_2705 43 105 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 105 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 105 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 105 151 (accept_3_3 41 105 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 105 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 105 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 105 151
  (Polychromatic418967fa.accept_9_3_6_7_1_562 39 105 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 105 151 (accept_3_3 38 105 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 105 151 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 105 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 105 151 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 105 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 105 151 (accept_3_3 35 105 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 105 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 105 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 105 151
  (Polychromatic418967fa.accept_13_7_1_8_1_1778 33 105 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 105 151 (accept_3_3 32 105 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 105 151 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 105 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 105 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 105 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 105 151 (accept_3_3 29 105 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 105 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 105 151
  (Polychromatic418967fa.accept_12_3_9_7_1_472 27 105 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 105 151 (accept_3_3 26 105 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 105 151 (Polychromatic418967fa.accept_11_3_6_8_1_1924 25 105 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 105 151 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 105 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 105 151 (accept_3_3 23 105 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 105 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 105 151
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 105 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 105 151 (accept_3_3 20 105 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 105 151 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 105 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 105 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 105 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 151 (accept_3_3 17 105 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 105 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 105 151
  (Polychromatic418967fa.accept_12_3_9_7_1_472 15 105 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 105 151 (accept_3_3 14 105 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 105 151 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 105 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 105 151 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 105 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 151 (accept_3_3 11 105 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 105 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 105 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 105 151
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 105 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 105 151 (accept_3_3 8 105 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  105 151 (Polychromatic418967fa.accept_13_7_1_8_1_1778 7 105 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 105 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 105 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 105 151 (accept_3_3 5 105 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 105 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 151
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 105 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 105 151 (accept_3_3 2 105 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  105 151 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 105 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 105 151))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 104 151 (Eq.refl
  Bool.true) (allA_of_3_1 48 104 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 103 151 (Eq.refl Bool.true)
  (allA_succ_of_accept 48 103 151 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 103 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 103 151 (accept_3_3 47 103 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 103 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 103 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 103 151 (Polychromatic418967fa.accept_11_1_4_8_1_1918
  45 103 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 103 151 (accept_3_3 44
  103 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 103 151
  (Polychromatic418967fa.accept_7_1_5_4_1_134 43 103 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 103 151 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 103 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 103 151 (accept_3_3 41 103 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 103 151 (Polychromatic418967fa.accept_11_7_4_8_1_1371 40 103 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 103 151
  (Polychromatic418967fa.accept_9_3_4_7_1_89 39 103 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 103 151 (accept_3_3 38 103 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 103 151 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 103 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 103 151 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 103 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 103 151 (accept_3_3 35 103 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 103 151 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 103 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 103 151
  (Polychromatic418967fa.accept_9_6_4_7_1_300 33 103 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 103 151 (accept_3_3 32 103 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 103 151 (Polychromatic418967fa.accept_13_5_12_8_1_198 31 103 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 103 151 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 103 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 103 151 (accept_3_3 29 103 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 103 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 103 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 103 151
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 103 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 103 151 (accept_3_3 26 103 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 103 151 (Polychromatic418967fa.accept_15_10_13_1_1_3698 25 103 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 103 151 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 103 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 103 151 (accept_3_3 23 103 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 103 151 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 103 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 103 151
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 103 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 103 151 (accept_3_3 20 103 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 103 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 103 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 103 151 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 103 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 103 151 (accept_3_3 17 103 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 103 151 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 103 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 103 151
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 103 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 103 151 (accept_3_3 14 103 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 103 151 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 103 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 103 151 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 103 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 103 151 (accept_3_3 11 103 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 103 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 103 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 103 151
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 103 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 103 151 (accept_3_3 8 103 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  103 151 (Polychromatic418967fa.accept_11_7_4_8_1_1371 7 103 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 103 151 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 103 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 103 151 (accept_3_3 5 103 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 103 151 (Polychromatic418967fa.accept_13_4_12_8_1_197 4 103 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 103 151
  (Polychromatic418967fa.accept_9_3_4_7_1_89 3 103 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 103 151 (accept_3_3 2 103 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  103 151 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 103 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 103 151))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 102 151 (Eq.refl
  Bool.true) (allA_succ_of_accept 49 102 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 102 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 102 151 (Polychromatic418967fa.accept_13_9_11_8_1_195
  48 102 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 102 151 (accept_3_3 47
  102 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 102 151
  (Polychromatic418967fa.accept_9_1_3_7_1_6 46 102 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 102 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 102 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 102 151 (accept_3_3 44 102 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 102 151 (Polychromatic418967fa.accept_10_3_2_1_1_839 43 102 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 102 151
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 102 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 102 151 (accept_3_3 41 102 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 102 151 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 102 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 102 151 (Polychromatic418967fa.accept_10_9_2_1_1_840 39 102 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 102 151 (accept_3_3 38 102 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 102 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 102 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 102 151
  (Polychromatic418967fa.accept_10_6_2_1_1_494 36 102 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 102 151 (accept_3_3 35 102 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 102 151 (Polychromatic418967fa.accept_15_4_12_1_1_1081 34 102 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 102 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 102 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 102 151 (accept_3_3 32 102 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 102 151 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 102 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 102 151
  (Polychromatic418967fa.accept_13_4_11_8_1_1768 30 102 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 102 151 (accept_3_3 29 102 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 102 151 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 102 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 102 151 (Polychromatic418967fa.accept_11_5_3_8_1_454 27 102 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 102 151 (accept_3_3 26 102 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 102 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 102 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 102 151
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 102 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 102 151 (accept_3_3 23 102 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 102 151 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 102 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 102 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 102 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 102 151 (accept_3_3 20 102 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 102 151 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 102 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 102 151
  (Polychromatic418967fa.accept_24_18_6_7_1_8150 18 102 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 102 151 (accept_3_3 17 102 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 102 151 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 102 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 102 151 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 102 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 102 151 (accept_3_3 14 102 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 102 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 102 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 102 151
  (Polychromatic418967fa.accept_19_12_7_18_1_8110 12 102 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 102 151 (accept_3_3 11 102 151 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 102 151 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 102 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 102 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 102 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 102 151 (accept_3_3 8 102 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 102 151 (Polychromatic418967fa.accept_14_7_4_11_1_3038
  7 102 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 102 151
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 102 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 102 151 (accept_3_3 5 102 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  102 151 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 102 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 102 151 (Polychromatic418967fa.accept_10_3_2_1_1_839 3 102 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 102 151 (accept_3_3 2 102 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 102 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 102 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  151)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 101 151 (Eq.refl Bool.true) (allA_of_3_1 51 101
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 52 100 151 (Eq.refl Bool.true) (allA_succ_of_accept 51 100
  151 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 100 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 100 151 (accept_3_3 50 100 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 100 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 100 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 100 151 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 100 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 100 151 (accept_3_3 47 100 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 100 151 (Polychromatic418967fa.accept_12_10_4_7_1_948 46 100 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 100 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 100 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 100 151 (accept_3_3 44 100 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 100 151 (Polychromatic418967fa.accept_8_3_4_7_1_475 43 100 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 100 151 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 100 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 100 151 (accept_3_3 41 100 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 100 151 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 100 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 100 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 100 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 100 151 (accept_3_3 38 100 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 100 151 (Polychromatic418967fa.accept_11_4_1_8_1_1366 37 100 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 100 151 (Polychromatic418967fa.accept_15_6_10_1_1_3675 36 100 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 100 151 (accept_3_3 35 100 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 100 151 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 100 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 100 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 100 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 100 151 (accept_3_3 32 100 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 100 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 100 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 100 151 (Polychromatic418967fa.accept_9_3_1_7_1_97 30 100 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 100 151 (accept_3_3 29 100 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 100 151 (Polychromatic418967fa.accept_15_13_10_1_1_1862 28 100 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 100 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 100 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 100 151 (accept_3_3 26 100 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 100 151 (Polychromatic418967fa.accept_13_12_9_8_1_2595 25 100 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 100 151 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 100 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 100 151 (accept_3_3 23 100 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 100 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 100 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 100 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 100 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 100 151 (accept_3_3 20 100 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 100 151 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 100 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 100 151 (Polychromatic418967fa.accept_23_18_8_13_1_8149 18 100 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 100 151 (accept_3_3 17 100 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 100 151 (Polychromatic418967fa.accept_13_3_9_8_1_4202 16 100
  151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 100 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 100 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 100 151 (accept_3_3 14 100 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 100 151 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 100 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 100 151 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 100 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 100 151 (accept_3_3 11 100 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 100 151 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 100 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 100 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 100 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 100 151 (accept_3_3 8 100 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  100 151 (Polychromatic418967fa.accept_13_7_9_8_1_188 7 100 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 100 151 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 100 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 100 151 (accept_3_3 5 100 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 100 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 100 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 100 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 100 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 100 151 (accept_3_3 2 100 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  100 151 (Polychromatic418967fa.accept_13_1_9_8_1_1734 1 100 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 100 151)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 99 151 (Eq.refl
  Bool.true) (allA_succ_of_accept 52 99 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 99 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 151 (Polychromatic418967fa.accept_15_6_9_1_1_1823
  51 99 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 99 151 (accept_3_3 50
  99 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 99 151
  (Polychromatic418967fa.accept_19_11_4_18_1_5226 49 99 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 99 151 (Polychromatic418967fa.accept_10_8_9_1_1_189 48 99 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 99 151 (accept_3_3 47 99 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 99 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 99 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 151 (Polychromatic418967fa.accept_7_3_1_4_1_121 45
  99 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 99 151 (accept_3_3 44 99
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 99 151
  (Polychromatic418967fa.accept_16_11_3_7_1_2375 43 99 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 99 151 (Polychromatic418967fa.accept_10_2_9_1_1_185 42 99 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 99 151 (accept_3_3 41 99 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 99 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 99 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 151 (Polychromatic418967fa.accept_18_3_9_7_1_1839
  39 99 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 99 151 (accept_3_3 38
  99 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 99 151
  (Polychromatic418967fa.accept_15_7_9_1_1_473 37 99 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 99 151 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 99 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 99 151 (accept_3_3 35 99 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 99 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 99 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 151 (Polychromatic418967fa.accept_7_5_1_4_1_122 33
  99 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 99 151 (accept_3_3 32 99
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 151
  (Polychromatic418967fa.accept_7_3_1_4_1_121 31 99 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 99 151 (Polychromatic418967fa.accept_19_11_4_18_1_5226 30 99 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 151 (accept_3_3 29 99 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 99 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 99 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 151 (Polychromatic418967fa.accept_16_11_3_7_1_2375
  27 99 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 99 151 (accept_3_3 26
  99 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 151
  (Polychromatic418967fa.accept_10_5_9_1_1_187 25 99 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 99 151 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 99 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 99 151 (accept_3_3 23 99 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 99 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 99 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 151 (Polychromatic418967fa.accept_12_9_3_7_1_924
  21 99 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 99 151 (accept_3_3 20
  99 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 99 151
  (Polychromatic418967fa.accept_7_5_1_4_1_122 19 99 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 99 151 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 99 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 151 (accept_3_3 17 99 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 99 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 99 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 151 (Polychromatic418967fa.accept_10_5_9_1_1_187
  15 99 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 99 151 (accept_3_3 14
  99 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 151
  (Polychromatic418967fa.accept_22_13_11_19_1_8148 13 99 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 99 151 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 99 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 99 151 (accept_3_3 11 99 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 99 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 151
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 99 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 99 151 (accept_3_3 8 99 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99
  151 (Polychromatic418967fa.accept_15_7_9_1_1_473 7 99 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 99 151 (Polychromatic418967fa.accept_15_6_9_1_1_1823 6 99 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 151 (accept_3_3 5 99 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 99 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 99 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99 151 (Polychromatic418967fa.accept_7_3_1_4_1_121 3
  99 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 151 (accept_3_3 2 99 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 151 (Polychromatic418967fa.accept_22_1_11_19_1_6441
  1 99 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  151))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 98 151 (Eq.refl Bool.true) (allA_of_3_1 54 98
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 55 97 151 (Eq.refl Bool.true) (allA_succ_of_accept 54 97 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 97 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 97 151 (accept_3_3 53 97 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  97 151 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 97 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 97 151 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 97 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 97 151 (accept_3_3 50 97 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 97 151 (Polychromatic418967fa.accept_21_7_13_4_1_2169 49 97 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 97 151
  (Polychromatic418967fa.accept_17_14_12_15_1_5558 48 97 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 97 151 (accept_3_3 47 97 151 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 97 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 97 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 97 151 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 97 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 97 151 (accept_3_3 44 97 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 97 151 (Polychromatic418967fa.accept_11_10_9_8_1_1974
  43 97 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 97 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 97 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 97 151 (accept_3_3 41 97 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  97 151 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 97 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 97 151 (Polychromatic418967fa.accept_15_9_7_1_1_1075 39 97 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 97 151 (accept_3_3 38 97 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 97 151 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 97 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 97 151
  (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 97 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 97 151 (accept_3_3 35 97 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  97 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 97 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 97 151 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 97 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 97 151 (accept_3_3 32 97 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 97 151 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 97 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 97 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 97 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 97 151 (accept_3_3 29 97 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  97 151 (Polychromatic418967fa.accept_13_2_6_8_1_1092 28 97 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 97 151 (Polychromatic418967fa.accept_13_1_6_8_1_208 27 97 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 97 151 (accept_3_3 26 97 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 97 151 (Polychromatic418967fa.accept_15_10_7_1_1_3686 25 97 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 97 151
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 97 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 97 151 (accept_3_3 23 97 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  97 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 97 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 97 151 (Polychromatic418967fa.accept_11_10_9_8_1_1974 21 97 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 97 151 (accept_3_3 20 97 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 97 151 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 97 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 97 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 97 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 97 151 (accept_3_3 17 97 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  97 151 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 97 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 97 151 (Polychromatic418967fa.accept_13_2_6_8_1_1092 15 97 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 97 151 (accept_3_3 14 97 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 97 151 (Polychromatic418967fa.accept_24_13_1_7_1_8147 13 97 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 97 151
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 97 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 97 151 (accept_3_3 11 97 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  97 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 97 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 97 151 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 97 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 151 (accept_3_3 8 97 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 97 151 (Polychromatic418967fa.accept_21_7_13_4_1_2169 7 97 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 97 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 97 151 (accept_3_3 5 97 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97
  151 (Polychromatic418967fa.accept_10_4_7_1_1_471 4 97 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 97 151 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 97 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 151 (accept_3_3 2 97 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 97 151 (Polychromatic418967fa.accept_13_1_6_8_1_208 1 97 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97 151)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 56 96 151 (Eq.refl Bool.true) (allA_succ_of_accept 55 96 151 (Polychromatic418967fa.accept_7_6_5_4_1_297
  55 96 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 96 151
  (Polychromatic418967fa.accept_15_9_6_1_1_493 54 96 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 96 151 (accept_3_3 53 96 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  96 151 (Polychromatic418967fa.accept_10_2_6_1_1_1296 52 96 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 96 151 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 96 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 96 151 (accept_3_3 50 96 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 96 151 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 96 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 96 151
  (Polychromatic418967fa.accept_7_6_5_4_1_297 48 96 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 96 151 (accept_3_3 47 96 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  96 151 (Polychromatic418967fa.accept_9_1_6_7_1_285 46 96 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 96 151 (Polychromatic418967fa.accept_10_5_6_1_1_836 45 96 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 96 151 (accept_3_3 44 96 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 96 151 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 96 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 96 151
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 96 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 96 151 (accept_3_3 41 96 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  96 151 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 96 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 96 151 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 96 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 96 151 (accept_3_3 38 96 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 96 151 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 96 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 96 151
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 96 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 96 151 (accept_3_3 35 96 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  96 151 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 96 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 96 151 (Polychromatic418967fa.accept_15_3_6_1_1_1834 33 96 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 96 151 (accept_3_3 32 96 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 96 151 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 96 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 96 151
  (Polychromatic418967fa.accept_7_2_5_4_1_115 30 96 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 96 151 (accept_3_3 29 96 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  96 151 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 96 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 96 151 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 96 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 96 151 (accept_3_3 26 96 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 96 151 (Polychromatic418967fa.accept_10_5_6_1_1_836 25 96 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 96 151
  (Polychromatic418967fa.accept_15_9_6_1_1_493 24 96 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 96 151 (accept_3_3 23 96 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  96 151 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 96 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 96 151 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 96 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 96 151 (accept_3_3 20 96 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 151 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 96 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 96 151
  (Polychromatic418967fa.accept_15_3_6_1_1_1834 18 96 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 96 151 (accept_3_3 17 96 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  96 151 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 96 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 96 151 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 96 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 96 151 (accept_3_3 14 96 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 151 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 96 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 96 151
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 96 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 96 151 (accept_3_3 11 96 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  96 151 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 96 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 96 151 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 96 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 96 151 (accept_3_3 8 96 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 151 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 96 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 96 151
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 96 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 96 151 (accept_3_3 5 96 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 96
  151 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 96 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 96 151 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 96 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 96 151 (accept_3_3 2 96 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 96 151 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 96 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96 151))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 57 95 151 (Eq.refl Bool.true) (allA_of_3_1 57 95 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  58 94 151 (Eq.refl Bool.true) (allA_succ_of_accept 57 94 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 94 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 94 151 (accept_3_3 56 94 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 94 151 (Polychromatic418967fa.accept_7_6_3_4_1_294 55
  94 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 94 151
  (Polychromatic418967fa.accept_25_4_19_1_1_8146 54 94 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 94 151 (accept_3_3 53 94 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  94 151 (Polychromatic418967fa.accept_12_4_10_7_1_149 52 94 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 94 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 94 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 94 151 (accept_3_3 50 94 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 94 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 94 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 94 151
  (Polychromatic418967fa.accept_7_6_3_4_1_294 48 94 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 94 151 (accept_3_3 47 94 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  94 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 94 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 94 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 94 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 94 151 (accept_3_3 44 94 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 94 151 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 94 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 94 151
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 94 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 94 151 (accept_3_3 41 94 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  94 151 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 94 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 94 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 94 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 94 151 (accept_3_3 38 94 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 94 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 94 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 94 151
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 94 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 94 151 (accept_3_3 35 94 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  94 151 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 94 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 94 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 94 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 94 151 (accept_3_3 32 94 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 94 151 (Polychromatic418967fa.accept_13_5_3_8_1_1117 31 94 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 94 151
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 94 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 94 151 (accept_3_3 29 94 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  94 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 94 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 94 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 94 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 94 151 (accept_3_3 26 94 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 94 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 94 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 94 151
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 94 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 94 151 (accept_3_3 23 94 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  94 151 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 94 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 94 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 94 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 94 151 (accept_3_3 20 94 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 94 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 94 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 94 151
  (Polychromatic418967fa.accept_13_5_3_8_1_1117 18 94 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 94 151 (accept_3_3 17 94 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  94 151 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 94 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 94 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 94 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 94 151 (accept_3_3 14 94 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 94 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 94 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 94 151
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 94 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 94 151 (accept_3_3 11 94 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  94 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 94 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 94 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 94 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 94 151 (accept_3_3 8 94 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 94 151 (Polychromatic418967fa.accept_10_7_4_1_1_1319 7 94 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 94 151
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 94 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 94 151 (accept_3_3 5 94 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 94
  151 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 94 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 94 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 94 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 94 151 (accept_3_3 2 94 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 94 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 94 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94
  151)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 93 151 (Eq.refl Bool.true)
  (allA_succ_of_accept 58 93 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 93 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 151 (Polychromatic418967fa.accept_11_2_5_8_1_470 57 93 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 93 151 (accept_3_3 56 93 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 93 151 (Polychromatic418967fa.accept_7_6_2_4_1_291 55
  93 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 93 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 93 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 93 151 (accept_3_3 53 93 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  93 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 93 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 93 151 (Polychromatic418967fa.accept_9_6_3_7_1_580 51 93 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 93 151 (accept_3_3 50 93 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 93 151 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 93 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 93 151
  (Polychromatic418967fa.accept_7_6_2_4_1_291 48 93 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 93 151 (accept_3_3 47 93 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  93 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 93 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 93 151 (Polychromatic418967fa.accept_13_6_2_8_1_1782 45 93 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 93 151 (accept_3_3 44 93 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 93 151 (Polychromatic418967fa.accept_15_13_3_1_1_3740 43 93 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 93 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 93 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 93 151 (accept_3_3 41 93 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  93 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 93 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 93 151 (Polychromatic418967fa.accept_12_3_9_7_1_472 39 93 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 93 151 (accept_3_3 38 93 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 93 151 (Polychromatic418967fa.accept_9_1_3_7_1_6 37 93 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 93 151
  (Polychromatic418967fa.accept_11_3_5_8_1_458 36 93 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 93 151 (accept_3_3 35 93 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  93 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 93 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 93 151 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 93 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 93 151 (accept_3_3 32 93 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 93 151 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 93 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 93 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 93 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 93 151 (accept_3_3 29 93 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  93 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 93 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 93 151 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 93 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 151 (accept_3_3 26 93 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 93 151 (Polychromatic418967fa.accept_11_3_5_8_1_458 25 93 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 93 151
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 93 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 93 151 (accept_3_3 23 93 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  93 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 93 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 93 151 (Polychromatic418967fa.accept_15_6_3_1_1_3678 21 93 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 151 (accept_3_3 20 93 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 151 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 93 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 93 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 93 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 93 151 (accept_3_3 17 93 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  93 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 93 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 93 151 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 93 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 151 (accept_3_3 14 93 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 151 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 93 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 93 151
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 93 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 93 151 (accept_3_3 11 93 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  93 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 93 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 93 151 (Polychromatic418967fa.accept_16_9_13_7_1_1509 9 93 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 151 (accept_3_3 8 93 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 151 (Polychromatic418967fa.accept_13_7_2_8_1_1746 7 93 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 93 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 151 (accept_3_3 5 93 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93
  151 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 93 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 93 151 (Polychromatic418967fa.accept_11_3_5_8_1_458 3 93 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 151 (accept_3_3 2 93 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 93 151 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 93 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93 151)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 60 92 151 (Eq.refl Bool.true) (allA_of_3_1 60 92 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  61 91 151 (Eq.refl Bool.true) (allA_succ_of_accept 60 91 151 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 91 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 91 151 (accept_3_3 59 91 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 91 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 58
  91 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 91 151
  (Polychromatic418967fa.accept_9_3_1_7_1_97 57 91 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 91 151 (accept_3_3 56 91 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  91 151 (Polychromatic418967fa.accept_21_13_7_4_1_4991 55 91 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 91 151 (Polychromatic418967fa.accept_19_16_15_18_1_5252 54 91 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 91 151 (accept_3_3 53 91 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 91 151 (Polychromatic418967fa.accept_8_4_3_7_1_491 52 91 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 91 151
  (Polychromatic418967fa.accept_9_6_1_7_1_577 51 91 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 91 151 (accept_3_3 50 91 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  91 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 91 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 91 151 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 91 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 91 151 (accept_3_3 47 91 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 91 151 (Polychromatic418967fa.accept_14_4_7_11_1_790 46 91 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 91 151
  (Polychromatic418967fa.accept_14_3_7_11_1_765 45 91 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 91 151 (accept_3_3 44 91 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  91 151 (Polychromatic418967fa.accept_17_9_6_15_1_5454 43 91 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 91 151 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 91 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 91 151 (accept_3_3 41 91 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 91 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 91 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 91 151
  (Polychromatic418967fa.accept_9_3_1_7_1_97 39 91 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 91 151 (accept_3_3 38 91 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  91 151 (Polychromatic418967fa.accept_16_5_11_7_1_5635 37 91 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 91 151 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 91 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 91 151 (accept_3_3 35 91 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 91 151 (Polychromatic418967fa.accept_16_2_11_7_1_2352 34 91 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 91 151
  (Polychromatic418967fa.accept_9_6_1_7_1_577 33 91 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 91 151 (accept_3_3 32 91 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  91 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 91 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 91 151 (Polychromatic418967fa.accept_9_3_1_7_1_97 30 91 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 91 151 (accept_3_3 29 91 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 91 151 (Polychromatic418967fa.accept_8_4_3_7_1_491 28 91 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 91 151
  (Polychromatic418967fa.accept_11_5_3_8_1_454 27 91 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 91 151 (accept_3_3 26 91 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  91 151 (Polychromatic418967fa.accept_17_8_6_15_1_523 25 91 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 91 151 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 91 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 91 151 (accept_3_3 23 91 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 91 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 91 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 91 151
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 91 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 91 151 (accept_3_3 20 91 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  91 151 (Polychromatic418967fa.accept_16_3_11_7_1_770 19 91 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 91 151 (Polychromatic418967fa.accept_14_4_7_11_1_790 18 91 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 91 151 (accept_3_3 17 91 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 91 151 (Polychromatic418967fa.accept_11_5_3_8_1_454 16 91 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 91 151
  (Polychromatic418967fa.accept_9_6_1_7_1_577 15 91 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 91 151 (accept_3_3 14 91 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  91 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 91 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 91 151 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 91 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 91 151 (accept_3_3 11 91 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 91 151 (Polychromatic418967fa.accept_14_10_7_11_1_3015 10 91 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 151
  (Polychromatic418967fa.accept_17_9_6_15_1_5454 9 91 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 91 151 (accept_3_3 8 91 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 91
  151 (Polychromatic418967fa.accept_19_7_15_18_1_8132 7 91 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 91 151 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 91 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 91 151 (accept_3_3 5 91 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 91 151 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 91 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 91 151
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 91 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 91 151 (accept_3_3 2 91 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 91
  151 (Polychromatic418967fa.accept_21_1_7_4_1_4947 1 91 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 91 151))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 90 151
  (Eq.refl Bool.true) (allA_succ_of_accept 61 90 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 90 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 90 151
  (Polychromatic418967fa.accept_11_5_2_8_1_866 60 90 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 90 151 (accept_3_3 59 90 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  90 151 (Polychromatic418967fa.accept_7_2_6_4_1_29 58 90 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 90 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 90 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 90 151 (accept_3_3 56 90 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 90 151 (Polychromatic418967fa.accept_20_15_10_11_1_8145 55 90 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 90 151
  (Polychromatic418967fa.accept_7_5_6_4_1_117 54 90 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 90 151 (accept_3_3 53 90 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  90 151 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 90 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 90 151 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 90 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 90 151 (accept_3_3 50 90 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 90 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 90 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 90 151
  (Polychromatic418967fa.accept_13_9_12_8_1_570 48 90 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 90 151 (accept_3_3 47 90 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  90 151 (Polychromatic418967fa.accept_13_7_12_8_1_199 46 90 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 90 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 90 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 90 151 (accept_3_3 44 90 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 90 151 (Polychromatic418967fa.accept_13_4_12_8_1_197 43 90 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 90 151
  (Polychromatic418967fa.accept_19_4_14_18_1_5234 42 90 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 90 151 (accept_3_3 41 90 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  90 151 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 90 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 90 151 (Polychromatic418967fa.accept_19_1_14_18_1_3919 39 90 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 90 151 (accept_3_3 38 90 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 90 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 90 151
  (Polychromatic418967fa.accept_13_10_12_8_1_2550 36 90 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 90 151 (accept_3_3 35 90 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  90 151 (Polychromatic418967fa.accept_19_15_14_18_1_6696 34 90 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 90 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 90 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 90 151 (accept_3_3 32 90 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 90 151 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 90 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 90 151
  (Polychromatic418967fa.accept_7_2_6_4_1_29 30 90 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 90 151 (accept_3_3 29 90 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  90 151 (Polychromatic418967fa.accept_17_11_5_15_1_8144 28 90 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 90 151 (Polychromatic418967fa.accept_11_5_2_8_1_866 27 90 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 90 151 (accept_3_3 26 90 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 90 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 90 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 90 151
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 90 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 90 151 (accept_3_3 23 90 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  90 151 (Polychromatic418967fa.accept_13_9_12_8_1_570 22 90 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 90 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 90 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 90 151 (accept_3_3 20 90 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 90 151 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 90 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 90 151
  (Polychromatic418967fa.accept_13_5_12_8_1_198 18 90 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 90 151 (accept_3_3 17 90 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  90 151 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 90 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 90 151 (Polychromatic418967fa.accept_19_15_14_18_1_6696 15 90 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 90 151 (accept_3_3 14 90 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 90 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 90 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 90 151
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 90 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 90 151 (accept_3_3 11 90 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  90 151 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 90 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 90 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 90 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 90 151 (accept_3_3 8 90 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 151 (Polychromatic418967fa.accept_13_7_12_8_1_199 7 90 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 90 151
  (Polychromatic418967fa.accept_22_6_2_19_1_8143 6 90 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 90 151 (accept_3_3 5 90 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 90
  151 (Polychromatic418967fa.accept_13_4_12_8_1_197 4 90 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 90 151 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 90 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 90 151 (accept_3_3 2 90 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 90 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 90 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  151)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 89 151 (Eq.refl Bool.true)
  (allA_of_3_1 63 89 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 64 88 151 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 88 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 88 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 88 151 (accept_3_3 62 88 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 88 151 (Polychromatic418967fa.accept_20_1_8_11_1_8097 61 88 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 88 151
  (Polychromatic418967fa.accept_16_12_8_7_1_4530 60 88 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 88 151 (accept_3_3 59 88 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  88 151 (Polychromatic418967fa.accept_12_10_4_7_1_948 58 88 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 88 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 88 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 88 151 (accept_3_3 56 88 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 88 151 (Polychromatic418967fa.accept_15_10_13_1_1_3698 55 88 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 88 151
  (Polychromatic418967fa.accept_13_2_10_8_1_1126 54 88 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 88 151 (accept_3_3 53 88 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  88 151 (Polychromatic418967fa.accept_16_4_8_7_1_3396 52 88 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 88 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 88 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 88 151 (accept_3_3 50 88 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 88 151 (Polychromatic418967fa.accept_10_9_8_1_1_1331 49 88 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 88 151
  (Polychromatic418967fa.accept_15_3_13_1_1_479 48 88 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 88 151 (accept_3_3 47 88 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  88 151 (Polychromatic418967fa.accept_12_10_4_7_1_948 46 88 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 88 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 88 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 88 151 (accept_3_3 44 88 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 88 151 (Polychromatic418967fa.accept_10_3_8_1_1_182 43 88 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 88 151
  (Polychromatic418967fa.accept_15_12_13_1_1_3695 42 88 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 88 151 (accept_3_3 41 88 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  88 151 (Polychromatic418967fa.accept_15_10_13_1_1_3698 40 88 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 88 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 88 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 88 151 (accept_3_3 38 88 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 88 151 (Polychromatic418967fa.accept_13_11_10_8_1_1804 37 88 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 88 151
  (Polychromatic418967fa.accept_14_8_4_11_1_3035 36 88 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 88 151 (accept_3_3 35 88 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  88 151 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 88 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 88 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 88 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 88 151 (accept_3_3 32 88 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 88 151 (Polychromatic418967fa.accept_13_5_10_8_1_1127 31 88 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 88 151
  (Polychromatic418967fa.accept_13_4_10_8_1_1817 30 88 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 88 151 (accept_3_3 29 88 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  88 151 (Polychromatic418967fa.accept_13_2_10_8_1_1126 28 88 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 88 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 88 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 88 151 (accept_3_3 26 88 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 88 151 (Polychromatic418967fa.accept_13_12_10_8_1_3343 25 88 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 88 151
  (Polychromatic418967fa.accept_13_11_10_8_1_1804 24 88 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 88 151 (accept_3_3 23 88 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  88 151 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 88 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 88 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 88 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 88 151 (accept_3_3 20 88 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 88 151 (Polychromatic418967fa.accept_10_9_8_1_1_1331 19 88 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 88 151
  (Polychromatic418967fa.accept_13_5_10_8_1_1127 18 88 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 88 151 (accept_3_3 17 88 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  88 151 (Polychromatic418967fa.accept_25_16_13_1_1_8142 16 88 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 88 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 88 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 88 151 (accept_3_3 14 88 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 88 151 (Polychromatic418967fa.accept_10_3_8_1_1_182 13 88 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 88 151
  (Polychromatic418967fa.accept_13_12_10_8_1_3343 12 88 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 88 151 (accept_3_3 11 88 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  88 151 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 88 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 88 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 88 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 88 151 (accept_3_3 8 88 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 88 151 (Polychromatic418967fa.accept_13_7_10_8_1_567 7 88 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 88 151
  (Polychromatic418967fa.accept_19_6_12_18_1_8141 6 88 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 88 151 (accept_3_3 5 88 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 88
  151 (Polychromatic418967fa.accept_13_4_10_8_1_1817 4 88 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 88 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 88 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 88 151 (accept_3_3 2 88 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 88 151 (Polychromatic418967fa.accept_14_1_4_11_1_3036 1 88 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88
  151)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 87 151 (Eq.refl Bool.true)
  (allA_succ_of_accept 64 87 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 87 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 151 (Polychromatic418967fa.accept_13_11_9_8_1_1125 63 87
  151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 87 151 (accept_3_3 62 87 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 87 151
  (Polychromatic418967fa.accept_17_10_2_15_1_3179 61 87 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 87 151 (Polychromatic418967fa.accept_19_3_11_18_1_2709 60 87 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 87 151 (accept_3_3 59 87 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 87 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 87 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 151 (Polychromatic418967fa.accept_7_1_3_4_1_128 57
  87 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 87 151 (accept_3_3 56 87
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 87 151
  (Polychromatic418967fa.accept_7_6_3_4_1_294 55 87 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 87 151 (Polychromatic418967fa.accept_10_4_7_1_1_471 54 87 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 87 151 (accept_3_3 53 87 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 87 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 87 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 151 (Polychromatic418967fa.accept_13_12_9_8_1_2595
  51 87 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 87 151 (accept_3_3 50
  87 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 151
  (Polychromatic418967fa.accept_9_4_6_7_1_286 49 87 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 87 151 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 87 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 87 151 (accept_3_3 47 87 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 87 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 87 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 151 (Polychromatic418967fa.accept_12_9_3_7_1_924
  45 87 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 87 151 (accept_3_3 44
  87 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 87 151
  (Polychromatic418967fa.accept_7_1_3_4_1_128 43 87 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 87 151 (Polychromatic418967fa.accept_11_9_10_8_1_444 42 87 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 87 151 (accept_3_3 41 87 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 87 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 87 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 151 (Polychromatic418967fa.accept_9_3_6_7_1_562 39
  87 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 87 151 (accept_3_3 38 87
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 87 151
  (Polychromatic418967fa.accept_9_1_6_7_1_285 37 87 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 87 151 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 87 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 87 151 (accept_3_3 35 87 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 87 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 87 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 151 (Polychromatic418967fa.accept_12_9_3_7_1_924
  33 87 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 87 151 (accept_3_3 32
  87 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 151
  (Polychromatic418967fa.accept_9_4_6_7_1_286 31 87 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 87 151 (Polychromatic418967fa.accept_9_3_6_7_1_562 30 87 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 151 (accept_3_3 29 87 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 87 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 87 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 151 (Polychromatic418967fa.accept_7_6_3_4_1_294 27
  87 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 87 151 (accept_3_3 26 87
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 151
  (Polychromatic418967fa.accept_13_12_9_8_1_2595 25 87 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 87 151 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 87 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 151 (accept_3_3 23 87 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 87 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 87 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 151 (Polychromatic418967fa.accept_9_3_6_7_1_562 21
  87 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 87 151 (accept_3_3 20 87
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 151
  (Polychromatic418967fa.accept_9_1_6_7_1_285 19 87 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 87 151 (Polychromatic418967fa.accept_20_18_7_11_1_3692 18 87 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 151 (accept_3_3 17 87 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 87 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 87 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 151 (Polychromatic418967fa.accept_7_1_3_4_1_128 15
  87 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 151 (accept_3_3 14 87
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 151
  (Polychromatic418967fa.accept_7_6_3_4_1_294 13 87 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 87 151 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 87 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 151 (accept_3_3 11 87 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 87 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 87 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 151 (Polychromatic418967fa.accept_11_9_10_8_1_444 9
  87 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 151 (accept_3_3 8 87 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 151 (Polychromatic418967fa.accept_13_7_9_8_1_188 7
  87 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87 151
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 87 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 87 151 (accept_3_3 5 87 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87
  151 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 87 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 87 151 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 87 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 151 (accept_3_3 2 87 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 87 151 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 87 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  151))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 86 151 (Eq.refl Bool.true)
  (allA_of_3_1 66 86 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 67 85 151 (Eq.refl Bool.true)
  (allA_succ_of_accept 66 85 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 85 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 85 151 (accept_3_3 65 85 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 85 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 85 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 85 151 (Polychromatic418967fa.accept_19_6_9_18_1_8140
  63 85 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 85 151 (accept_3_3 62
  85 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 85 151
  (Polychromatic418967fa.accept_7_5_1_4_1_122 61 85 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 85 151 (Polychromatic418967fa.accept_9_6_4_7_1_300 60 85 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 85 151 (accept_3_3 59 85 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 85 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 85 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 85 151 (Polychromatic418967fa.accept_9_3_4_7_1_89 57
  85 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 85 151 (accept_3_3 56 85
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 85 151 (Polychromatic418967fa.accept_9_1_4_7_1_7
  55 85 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 85 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 85 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 85 151 (accept_3_3 53 85 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  85 151 (Polychromatic418967fa.accept_7_3_1_4_1_121 52 85 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 85 151 (Polychromatic418967fa.accept_9_6_4_7_1_300 51 85 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 85 151 (accept_3_3 50 85 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 85 151 (Polychromatic418967fa.accept_10_9_5_1_1_1325 49 85 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 85 151
  (Polychromatic418967fa.accept_9_3_4_7_1_89 48 85 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 85 151 (accept_3_3 47 85 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  85 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 85 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 85 151 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 85 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 85 151 (accept_3_3 44 85 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 151 (Polychromatic418967fa.accept_15_13_10_1_1_1862 43 85 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 85 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 85 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 85 151 (accept_3_3 41 85 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  85 151 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 85 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 85 151 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 85 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 85 151 (accept_3_3 38 85 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 85 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 85 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 151
  (Polychromatic418967fa.accept_10_6_5_1_1_482 36 85 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 85 151 (accept_3_3 35 85 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  85 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 85 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 85 151 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 85 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 151 (accept_3_3 32 85 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 85 151 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 85 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 85 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 85 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 85 151 (accept_3_3 29 85 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  85 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 85 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 85 151 (Polychromatic418967fa.accept_13_1_7_8_1_1796 27 85 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 151 (accept_3_3 26 85 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 85 151 (Polychromatic418967fa.accept_13_12_7_8_1_1104 25 85 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 85 151
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 85 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 85 151 (accept_3_3 23 85 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  85 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 85 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 85 151 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 85 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 85 151 (accept_3_3 20 85 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 85 151 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 85 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 85 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 85 151 (accept_3_3 17 85 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  85 151 (Polychromatic418967fa.accept_10_6_5_1_1_482 16 85 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 85 151 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 85 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 85 151 (accept_3_3 14 85 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 151 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 85 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 151
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 85 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 151 (accept_3_3 11 85 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  85 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 85 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 85 151 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 85 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 151 (accept_3_3 8 85 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 151 (Polychromatic418967fa.accept_15_7_10_1_1_1836 7 85 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 85 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 85 151 (accept_3_3 5 85 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85
  151 (Polychromatic418967fa.accept_10_4_5_1_1_497 4 85 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 85 151 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 85 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 151 (accept_3_3 2 85 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 85 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 85 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  151))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 84 151 (Eq.refl Bool.true)
  (allA_succ_of_accept 67 84 151 (Polychromatic418967fa.accept_8_3_4_7_1_475 67 84 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 84 151 (Polychromatic418967fa.accept_13_1_6_8_1_208 66 84 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 84 151 (accept_3_3 65 84 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 84 151 (Polychromatic418967fa.accept_9_1_3_7_1_6 64
  84 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 84 151
  (Polychromatic418967fa.accept_13_11_6_8_1_1121 63 84 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 84 151 (accept_3_3 62 84 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  84 151 (Polychromatic418967fa.accept_16_13_4_7_1_1537 61 84 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 84 151 (Polychromatic418967fa.accept_9_6_3_7_1_580 60 84 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 84 151 (accept_3_3 59 84 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 84 151 (Polychromatic418967fa.accept_9_4_3_7_1_296 58 84 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 84 151
  (Polychromatic418967fa.accept_10_7_4_1_1_1319 57 84 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 84 151 (accept_3_3 56 84 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  84 151 (Polychromatic418967fa.accept_9_1_3_7_1_6 55 84 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 84 151 (Polychromatic418967fa.accept_13_2_6_8_1_1092 54 84 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 84 151 (accept_3_3 53 84 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 84 151 (Polychromatic418967fa.accept_15_7_9_1_1_473 52 84 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 84 151
  (Polychromatic418967fa.accept_8_3_4_7_1_475 51 84 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 84 151 (accept_3_3 50 84 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  84 151 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 84 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 84 151 (Polychromatic418967fa.accept_11_4_7_8_1_1926 48 84 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 84 151 (accept_3_3 47 84 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 84 151 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 84 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 84 151
  (Polychromatic418967fa.accept_10_5_4_1_1_842 45 84 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 84 151 (accept_3_3 44 84 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  84 151 (Polychromatic418967fa.accept_8_3_4_7_1_475 43 84 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 84 151 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 84 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 84 151 (accept_3_3 41 84 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 84 151 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 84 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 84 151
  (Polychromatic418967fa.accept_18_3_12_7_1_6728 39 84 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 84 151 (accept_3_3 38 84 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  84 151 (Polychromatic418967fa.accept_9_1_3_7_1_6 37 84 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 84 151 (Polychromatic418967fa.accept_15_6_9_1_1_1823 36 84 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 84 151 (accept_3_3 35 84 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 84 151 (Polychromatic418967fa.accept_23_11_15_13_1_6395 34 84 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 84 151
  (Polychromatic418967fa.accept_9_6_3_7_1_580 33 84 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 84 151 (accept_3_3 32 84 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  84 151 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 84 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 84 151 (Polychromatic418967fa.accept_16_14_4_7_1_2380 30 84 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 84 151 (accept_3_3 29 84 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 84 151 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 84 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 84 151
  (Polychromatic418967fa.accept_8_3_4_7_1_475 27 84 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 84 151 (accept_3_3 26 84 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  84 151 (Polychromatic418967fa.accept_10_5_4_1_1_842 25 84 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 84 151 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 84 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 84 151 (accept_3_3 23 84 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 84 151 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 84 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 84 151
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 21 84 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 84 151 (accept_3_3 20 84 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  84 151 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 84 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 84 151 (Polychromatic418967fa.accept_17_1_16_15_1_4315 18 84 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 84 151 (accept_3_3 17 84 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 84 151 (Polychromatic418967fa.accept_19_16_8_18_1_8139 16 84
  151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 84 151
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 84 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 84 151 (accept_3_3 14 84 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  84 151 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 84 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 84 151 (Polychromatic418967fa.accept_16_12_4_7_1_3391 12 84 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 84 151 (accept_3_3 11 84 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 84 151 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 84 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 84 151
  (Polychromatic418967fa.accept_19_9_8_18_1_1571 9 84 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 84 151 (accept_3_3 8 84 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 84
  151 (Polychromatic418967fa.accept_10_7_4_1_1_1319 7 84 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 84 151 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 84 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 84 151 (accept_3_3 5 84 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 84 151 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 84 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 84 151
  (Polychromatic418967fa.accept_8_3_4_7_1_475 3 84 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 84 151 (accept_3_3 2 84 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84
  151 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 84 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 84 151)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 83 151 (Eq.refl
  Bool.true) (allA_of_3_1 69 83 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 70 82 151 (Eq.refl Bool.true)
  (allA_succ_of_accept 69 82 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 82 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 82 151 (accept_3_3 68 82 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 82 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 67 82 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 82 151 (Polychromatic418967fa.accept_9_3_1_7_1_97 66
  82 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 82 151 (accept_3_3 65 82
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 82 151
  (Polychromatic418967fa.accept_7_1_5_4_1_134 64 82 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 82 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 82 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 82 151 (accept_3_3 62 82 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 82 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 82 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 82 151 (Polychromatic418967fa.accept_9_6_1_7_1_577 60
  82 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 82 151 (accept_3_3 59 82
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 82 151
  (Polychromatic418967fa.accept_7_2_5_4_1_115 58 82 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 82 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 82 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 82 151 (accept_3_3 56 82 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 82 151 (Polychromatic418967fa.accept_7_6_5_4_1_297 55 82 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 82 151 (Polychromatic418967fa.accept_15_9_7_1_1_1075
  54 82 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 82 151 (accept_3_3 53
  82 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 82 151
  (Polychromatic418967fa.accept_12_4_10_7_1_149 52 82 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 82 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 82 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 82 151 (accept_3_3 50 82 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 82 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 82 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 82 151 (Polychromatic418967fa.accept_7_6_5_4_1_297 48
  82 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 82 151 (accept_3_3 47 82
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 82 151
  (Polychromatic418967fa.accept_10_6_2_1_1_494 46 82 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 82 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 82 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 82 151 (accept_3_3 44 82 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 82 151 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 82 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 82 151 (Polychromatic418967fa.accept_9_6_1_7_1_577 42
  82 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 82 151 (accept_3_3 41 82
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 82 151
  (Polychromatic418967fa.accept_9_4_1_7_1_293 40 82 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 82 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 82 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 82 151 (accept_3_3 38 82 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 82 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 82 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 82 151 (Polychromatic418967fa.accept_7_1_5_4_1_134 36
  82 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 82 151 (accept_3_3 35 82
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 82 151
  (Polychromatic418967fa.accept_7_6_5_4_1_297 34 82 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 82 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 82 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 82 151 (accept_3_3 32 82 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 82 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 82 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 82 151 (Polychromatic418967fa.accept_7_2_5_4_1_115 30
  82 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 82 151 (accept_3_3 29 82
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 82 151
  (Polychromatic418967fa.accept_12_4_10_7_1_149 28 82 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 82 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 82 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 82 151 (accept_3_3 26 82 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 82 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 82 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 82 151 (Polychromatic418967fa.accept_9_6_1_7_1_577 24
  82 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 82 151 (accept_3_3 23 82
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 82 151
  (Polychromatic418967fa.accept_7_1_5_4_1_134 22 82 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 82 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 82 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 82 151 (accept_3_3 20 82 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 82 151 (Polychromatic418967fa.accept_10_9_2_1_1_840 19 82 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 82 151
  (Polychromatic418967fa.accept_21_18_19_4_1_4979 18 82 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 82 151 (accept_3_3 17 82 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  82 151 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 82 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 82 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 82 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 82 151 (accept_3_3 14 82 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 82 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 82 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 82 151
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 82 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 82 151 (accept_3_3 11 82 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  82 151 (Polychromatic418967fa.accept_13_10_4_8_1_2570 10 82 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 82 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 82 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 82 151 (accept_3_3 8 82 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 82 151 (Polychromatic418967fa.accept_19_7_6_18_1_8123 7 82 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 82 151
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 82 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 82 151 (accept_3_3 5 82 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 82
  151 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 82 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 82 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 82 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 151 (accept_3_3 2 82 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 82 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 82 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  151)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 81 151 (Eq.refl Bool.true)
  (allA_succ_of_accept 70 81 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 81 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 151 (Polychromatic418967fa.accept_15_9_6_1_1_493 69 81 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 81 151 (accept_3_3 68 81 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 81 151 (Polychromatic418967fa.accept_11_1_4_8_1_1918
  67 81 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 81 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 81 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 81 151 (accept_3_3 65 81 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  81 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 81 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 81 151 (Polychromatic418967fa.accept_12_3_9_7_1_472 63 81 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 81 151 (accept_3_3 62 81 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 151 (Polychromatic418967fa.accept_13_9_3_8_1_573 61 81 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 81 151
  (Polychromatic418967fa.accept_18_6_9_7_1_2905 60 81 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 81 151 (accept_3_3 59 81 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  81 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 81 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 81 151 (Polychromatic418967fa.accept_13_5_3_8_1_1117 57 81 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 81 151 (accept_3_3 56 81 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 151 (Polychromatic418967fa.accept_15_10_6_1_1_3707 55 81 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 81 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 81 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 81 151 (accept_3_3 53 81 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  81 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 81 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 81 151 (Polychromatic418967fa.accept_11_7_4_8_1_1371 51 81 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 81 151 (accept_3_3 50 81 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 81 151 (Polychromatic418967fa.accept_21_7_18_4_1_5024 49 81 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 81 151
  (Polychromatic418967fa.accept_13_9_3_8_1_573 48 81 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 81 151 (accept_3_3 47 81 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  81 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 81 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 81 151 (Polychromatic418967fa.accept_11_1_4_8_1_1918 45 81 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 81 151 (accept_3_3 44 81 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 151 (Polychromatic418967fa.accept_21_1_18_4_1_4975 43 81 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 81 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 81 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 81 151 (accept_3_3 41 81 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  81 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 81 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 81 151 (Polychromatic418967fa.accept_12_3_9_7_1_472 39 81 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 81 151 (accept_3_3 38 81 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 151 (Polychromatic418967fa.accept_13_11_3_8_1_1786 37 81 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 81 151
  (Polychromatic418967fa.accept_17_2_13_15_1_4349 36 81 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 81 151 (accept_3_3 35 81 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  81 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 81 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 81 151 (Polychromatic418967fa.accept_13_7_3_8_1_1750 33 81 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 81 151 (accept_3_3 32 81 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 151 (Polychromatic418967fa.accept_13_5_3_8_1_1117 31 81 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 81 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 81 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 81 151 (accept_3_3 29 81 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  81 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 81 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 81 151 (Polychromatic418967fa.accept_12_3_9_7_1_472 27 81 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 81 151 (accept_3_3 26 81 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 151 (Polychromatic418967fa.accept_15_10_6_1_1_3707 25 81 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 81 151
  (Polychromatic418967fa.accept_13_11_3_8_1_1786 24 81 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 81 151 (accept_3_3 23 81 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  81 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 81 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 81 151 (Polychromatic418967fa.accept_18_3_9_7_1_1839 21 81 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 81 151 (accept_3_3 20 81 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 151 (Polychromatic418967fa.accept_17_2_13_15_1_4349 19 81 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 81 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 81 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 81 151 (accept_3_3 17 81 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  81 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 81 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 81 151 (Polychromatic418967fa.accept_12_3_9_7_1_472 15 81 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 81 151 (accept_3_3 14 81 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 151 (Polychromatic418967fa.accept_19_13_5_18_1_8106 13 81 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 81 151
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 12 81 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 81 151 (accept_3_3 11 81 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  81 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 81 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 81 151 (Polychromatic418967fa.accept_13_9_3_8_1_573 9 81 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 81 151 (accept_3_3 8 81 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 151 (Polychromatic418967fa.accept_11_7_4_8_1_1371 7 81 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 81 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 81 151 (accept_3_3 5 81 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81
  151 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 81 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 81 151 (Polychromatic418967fa.accept_12_3_9_7_1_472 3 81 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 151 (accept_3_3 2 81 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 81 151 (Polychromatic418967fa.accept_11_1_4_8_1_1918 1 81 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81
  151))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 80 151 (Eq.refl Bool.true)
  (allA_of_3_1 72 80 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 73 79 151 (Eq.refl Bool.true)
  (allA_succ_of_accept 72 79 151 (Polychromatic418967fa.accept_10_2_9_1_1_185 72 79 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 79 151 (accept_3_3 71 79 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 79 151 (Polychromatic418967fa.accept_13_5_1_8_1_1115 70 79 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 79 151 (Polychromatic418967fa.accept_7_6_2_4_1_291 69
  79 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 79 151 (accept_3_3 68 79
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 79 151
  (Polychromatic418967fa.accept_16_3_15_7_1_3417 67 79 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 79 151 (Polychromatic418967fa.accept_19_9_3_18_1_5263 66 79 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 79 151 (accept_3_3 65 79 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 79 151 (Polychromatic418967fa.accept_13_12_1_8_1_1779 64 79 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 79 151
  (Polychromatic418967fa.accept_13_11_1_8_1_1776 63 79 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 79 151 (accept_3_3 62 79 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  79 151 (Polychromatic418967fa.accept_7_5_2_4_1_126 61 79 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 79 151 (Polychromatic418967fa.accept_11_5_2_8_1_866 60 79 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 79 151 (accept_3_3 59 79 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 79 151 (Polychromatic418967fa.accept_10_8_9_1_1_189 58 79 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 79 151
  (Polychromatic418967fa.accept_13_5_1_8_1_1115 57 79 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 79 151 (accept_3_3 56 79 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  79 151 (Polychromatic418967fa.accept_7_6_2_4_1_291 55 79 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 79 151 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 79 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 79 151 (accept_3_3 53 79 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 79 151 (Polychromatic418967fa.accept_10_2_9_1_1_185 52 79 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 79 151
  (Polychromatic418967fa.accept_13_12_1_8_1_1779 51 79 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 79 151 (accept_3_3 50 79 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  79 151 (Polychromatic418967fa.accept_11_5_2_8_1_866 49 79 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 79 151 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 79 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 79 151 (accept_3_3 47 79 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 79 151 (Polychromatic418967fa.accept_13_7_1_8_1_1778 46 79 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 79 151
  (Polychromatic418967fa.accept_10_5_9_1_1_187 45 79 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 79 151 (accept_3_3 44 79 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  79 151 (Polychromatic418967fa.accept_16_11_15_7_1_5654 43 79 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 79 151 (Polychromatic418967fa.accept_10_2_9_1_1_185 42 79 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 79 151 (accept_3_3 41 79 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 79 151 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 79 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 79 151
  (Polychromatic418967fa.accept_17_5_11_15_1_5445 39 79 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 79 151 (accept_3_3 38 79 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  79 151 (Polychromatic418967fa.accept_13_11_1_8_1_1776 37 79 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 79 151 (Polychromatic418967fa.accept_27_9_25_16_1_8138 36 79 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 79 151 (accept_3_3 35 79 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 79 151 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 79 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 79 151
  (Polychromatic418967fa.accept_7_5_2_4_1_126 33 79 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 79 151 (accept_3_3 32 79 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  79 151 (Polychromatic418967fa.accept_13_5_1_8_1_1115 31 79 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 79 151 (Polychromatic418967fa.accept_14_2_9_11_1_3054 30 79 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 79 151 (accept_3_3 29 79 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 79 151 (Polychromatic418967fa.accept_10_8_9_1_1_189 28 79 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 79 151
  (Polychromatic418967fa.accept_7_6_2_4_1_291 27 79 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 79 151 (accept_3_3 26 79 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  79 151 (Polychromatic418967fa.accept_10_5_9_1_1_187 25 79 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 79 151 (Polychromatic418967fa.accept_13_11_1_8_1_1776 24 79 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 79 151 (accept_3_3 23 79 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 79 151 (Polychromatic418967fa.accept_10_2_9_1_1_185 22 79 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 79 151
  (Polychromatic418967fa.accept_17_4_11_15_1_3170 21 79 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 79 151 (accept_3_3 20 79 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  79 151 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 79 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 79 151 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 79 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 79 151 (accept_3_3 17 79 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 79 151 (Polychromatic418967fa.accept_11_5_2_8_1_866 16 79 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 79 151
  (Polychromatic418967fa.accept_10_5_9_1_1_187 15 79 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 79 151 (accept_3_3 14 79 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  79 151 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 79 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 79 151 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 79 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 79 151 (accept_3_3 11 79 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 79 151 (Polychromatic418967fa.accept_20_10_19_11_1_2384 10 79 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 79 151
  (Polychromatic418967fa.accept_13_9_1_8_1_1742 9 79 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 79 151 (accept_3_3 8 79 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 79
  151 (Polychromatic418967fa.accept_13_7_1_8_1_1778 7 79 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 79 151 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 79 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 79 151 (accept_3_3 5 79 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 79 151 (Polychromatic418967fa.accept_17_4_11_15_1_3170 4 79 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 79 151
  (Polychromatic418967fa.accept_15_3_4_1_1_1072 3 79 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 79 151 (accept_3_3 2 79 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 79
  151 (Polychromatic418967fa.accept_23_1_10_13_1_8137 1 79 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 79 151))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74
  78 151 (Eq.refl Bool.true) (allA_succ_of_accept 73 78 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 78 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 78 151
  (Polychromatic418967fa.accept_17_4_10_15_1_5444 72 78 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 78 151 (accept_3_3 71 78 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  78 151 (Polychromatic418967fa.accept_11_4_1_8_1_1366 70 78 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 78 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 78 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 78 151 (accept_3_3 68 78 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 151 (Polychromatic418967fa.accept_9_4_6_7_1_286 67 78 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 78 151
  (Polychromatic418967fa.accept_7_3_1_4_1_121 66 78 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 78 151 (accept_3_3 65 78 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  78 151 (Polychromatic418967fa.accept_9_1_6_7_1_285 64 78 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 78 151 (Polychromatic418967fa.accept_10_3_8_1_1_182 63 78 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 78 151 (accept_3_3 62 78 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 78 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 78 151
  (Polychromatic418967fa.accept_14_4_8_11_1_794 60 78 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 78 151 (accept_3_3 59 78 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  78 151 (Polychromatic418967fa.accept_9_4_6_7_1_286 58 78 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 78 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 78 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 78 151 (accept_3_3 56 78 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 78 151 (Polychromatic418967fa.accept_9_1_6_7_1_285 55 78 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 78 151
  (Polychromatic418967fa.accept_7_5_1_4_1_122 54 78 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 78 151 (accept_3_3 53 78 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  78 151 (Polychromatic418967fa.accept_7_3_1_4_1_121 52 78 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 78 151 (Polychromatic418967fa.accept_15_6_3_1_1_3678 51 78 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 78 151 (accept_3_3 50 78 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 78 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 78 151
  (Polychromatic418967fa.accept_9_3_6_7_1_562 48 78 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 78 151 (accept_3_3 47 78 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  78 151 (Polychromatic418967fa.accept_9_1_6_7_1_285 46 78 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 78 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 78 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 78 151 (accept_3_3 44 78 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 151 (Polychromatic418967fa.accept_10_3_8_1_1_182 43 78 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 78 151
  (Polychromatic418967fa.accept_16_10_14_7_1_2372 42 78 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 78 151 (accept_3_3 41 78 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  78 151 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 78 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 78 151 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 78 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 78 151 (accept_3_3 38 78 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 78 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 78 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 78 151
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 36 78 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 78 151 (accept_3_3 35 78 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  78 151 (Polychromatic418967fa.accept_15_4_3_1_1_487 34 78 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 78 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 78 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 78 151 (accept_3_3 32 78 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 151 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 78 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 78 151
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 78 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 78 151 (accept_3_3 29 78 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  78 151 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 78 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 78 151 (Polychromatic418967fa.accept_18_9_6_7_1_6719 27 78 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 78 151 (accept_3_3 26 78 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 78 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 78 151
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 78 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 78 151 (accept_3_3 23 78 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  78 151 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 78 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 78 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 78 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 78 151 (accept_3_3 20 78 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 151 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 78 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 151
  (Polychromatic418967fa.accept_14_4_8_11_1_794 18 78 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 78 151 (accept_3_3 17 78 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  78 151 (Polychromatic418967fa.accept_19_16_2_18_1_8136 16 78 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 78 151 (Polychromatic418967fa.accept_11_4_1_8_1_1366 15 78 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 78 151 (accept_3_3 14 78 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 78 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 78 151
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 78 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 78 151 (accept_3_3 11 78 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  78 151 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 78 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 78 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 78 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 78 151 (accept_3_3 8 78 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 151 (Polychromatic418967fa.accept_20_7_18_11_1_5080 7 78 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 78 151
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 6 78 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 78 151 (accept_3_3 5 78 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78
  151 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 78 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 78 151 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 78 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 78 151 (accept_3_3 2 78 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 78 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 78 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  151)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 77 151 (Eq.refl
  Bool.true) (allA_of_3_1 75 77 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 76 151 (allA_succ_of_accept 75
  76 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 76 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 76 151 (accept_3_3 74 76 151 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 76 151 (Polychromatic418967fa.accept_7_3_6_4_1_30 73 76 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 76 151 (Polychromatic418967fa.accept_7_2_6_4_1_29 72 76 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 76 151 (accept_3_3 71 76 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 76 151 (Polychromatic418967fa.accept_12_10_4_7_1_948
  70 76 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 76 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 76 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 76 151 (accept_3_3 68 76 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  76 151 (Polychromatic418967fa.accept_8_3_4_7_1_475 67 76 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 76 151 (Polychromatic418967fa.accept_7_3_6_4_1_30 66 76 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 76 151 (accept_3_3 65 76 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 76 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 76 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 76 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 76 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 76 151 (accept_3_3 62 76 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  76 151 (Polychromatic418967fa.accept_7_5_6_4_1_117 61 76 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 76 151 (Polychromatic418967fa.accept_9_6_4_7_1_300 60 76 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 76 151 (accept_3_3 59 76 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 76 151 (Polychromatic418967fa.accept_7_2_6_4_1_29 58 76 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 76 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 76 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 76 151 (accept_3_3 56 76 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  76 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 76 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 76 151 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 76 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 76 151 (accept_3_3 53 76 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 76 151 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 76 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 76 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 76 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 76 151 (accept_3_3 50 76 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  76 151 (Polychromatic418967fa.accept_13_10_11_8_1_1770 49 76 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 76 151 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 76 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 76 151 (accept_3_3 47 76 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 76 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 76 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 76 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 76 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 76 151 (accept_3_3 44 76 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  76 151 (Polychromatic418967fa.accept_8_3_4_7_1_475 43 76 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 76 151 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 76 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 76 151 (accept_3_3 41 76 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 76 151 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 76 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 76 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 76 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 76 151 (accept_3_3 38 76 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  76 151 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 76 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 76 151 (Polychromatic418967fa.accept_13_10_11_8_1_1770 36 76 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 76 151 (accept_3_3 35 76 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 76 151 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 76 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 76 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 76 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 76 151 (accept_3_3 32 76 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  76 151 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 76 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 76 151 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 76 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 76 151 (accept_3_3 29 76 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 76 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 76 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 76 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 76 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 76 151 (accept_3_3 26 76 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  76 151 (Polychromatic418967fa.accept_10_5_6_1_1_836 25 76 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 76 151 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 76 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 76 151 (accept_3_3 23 76 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 76 151 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 76 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 76 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 76 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 76 151 (accept_3_3 20 76 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  76 151 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 76 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 76 151 (Polychromatic418967fa.accept_16_2_12_7_1_3410 18 76 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 76 151 (accept_3_3 17 76 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 76 151 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 76 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 76 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 76 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 76 151 (accept_3_3 14 76 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  76 151 (Polychromatic418967fa.accept_17_13_8_15_1_8135 13 76 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 76 151 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 76 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 76 151 (accept_3_3 11 76 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 76 151 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 76 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 76 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 76 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 76 151 (accept_3_3 8 76 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 76
  151 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 76 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 76 151 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 76 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 76 151 (accept_3_3 5 76 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 76 151 (Polychromatic418967fa.accept_13_4_11_8_1_1768 4 76 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 76 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 76
  151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 76 151 (accept_3_3 2 76 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 76 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 76
  151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76
  151)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 151 (allA_succ_of_accept
  74 75 151 (accept_3_3 74 75 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 75 151
  (Polychromatic418967fa.accept_9_1_3_7_1_6 73 75 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 75 151 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 75 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 75 151 (accept_3_3 71 75 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 75 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 75 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 151 (Polychromatic418967fa.accept_7_6_5_4_1_297 69
  75 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 151 (accept_3_3 68 75
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 151
  (Polychromatic418967fa.accept_9_4_3_7_1_296 67 75 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 75 151 (Polychromatic418967fa.accept_10_6_5_1_1_482 66 75 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 75 151 (accept_3_3 65 75 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 75 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 75 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 151
  (Polychromatic418967fa.accept_13_11_10_8_1_1804 63 75 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 75 151 (accept_3_3 62 75 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  75 151 (Polychromatic418967fa.accept_21_19_12_4_1_8134 61 75 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 75 151 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 75 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 75 151 (accept_3_3 59 75 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 75 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 151
  (Polychromatic418967fa.accept_7_1_5_4_1_134 57 75 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 75 151 (accept_3_3 56 75 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  75 151 (Polychromatic418967fa.accept_7_6_5_4_1_297 55 75 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 75 151 (Polychromatic418967fa.accept_10_4_5_1_1_497 54 75 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 75 151 (accept_3_3 53 75 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 75 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 151
  (Polychromatic418967fa.accept_7_2_5_4_1_115 51 75 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 75 151 (accept_3_3 50 75 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  75 151 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 75 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 75 151 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 75 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 75 151 (accept_3_3 47 75 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 75 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 151
  (Polychromatic418967fa.accept_12_9_3_7_1_924 45 75 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 75 151 (accept_3_3 44 75 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  75 151 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 75 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 75 151 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 75 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 75 151 (accept_3_3 41 75 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 75 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 151
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 39 75 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 75 151 (accept_3_3 38 75 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  75 151 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 75 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 75 151 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 75 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 75 151 (accept_3_3 35 75 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 75 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 151
  (Polychromatic418967fa.accept_9_6_3_7_1_580 33 75 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 75 151 (accept_3_3 32 75 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  75 151 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 75 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 75 151 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 75 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 75 151 (accept_3_3 29 75 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 75 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 151
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 75 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 75 151 (accept_3_3 26 75 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  75 151 (Polychromatic418967fa.accept_13_12_10_8_1_3343 25 75 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 75 151 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 75 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 75 151 (accept_3_3 23 75 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 75 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 151
  (Polychromatic418967fa.accept_11_10_9_8_1_1974 21 75 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 75 151 (accept_3_3 20 75 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  75 151 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 75 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 75 151 (Polychromatic418967fa.accept_13_5_10_8_1_1127 18 75 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 151 (accept_3_3 17 75 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 75 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 151
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 75 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 75 151 (accept_3_3 14 75 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  75 151 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 75 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 75 151 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 75 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 151 (accept_3_3 11 75 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 75 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 151
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 75 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 75 151 (accept_3_3 8 75 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75
  151 (Polychromatic418967fa.accept_13_7_10_8_1_567 7 75 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 75 151 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 75 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 75 151 (accept_3_3 5 75 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 75 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 75 151
  (Polychromatic418967fa.accept_16_3_11_7_1_770 3 75 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 75 151 (accept_3_3 2 75 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75
  151 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 75 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 75 151))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 151
  (allA_of_3_1 74 74 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 73 151 (allA_succ_of_accept 72 73 151
  (Polychromatic418967fa.accept_10_2_3_1_1_481 72 73 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 73 151 (accept_3_3 71 73 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  73 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 73 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 73 151 (Polychromatic418967fa.accept_7_6_3_4_1_294 69 73 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 151 (accept_3_3 68 73 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 67 73 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 73 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 73 151 (accept_3_3 65 73 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  73 151 (Polychromatic418967fa.accept_7_1_3_4_1_128 64 73 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 73 151 (Polychromatic418967fa.accept_14_7_3_11_1_2199 63 73 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 151 (accept_3_3 62 73 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 151 (Polychromatic418967fa.accept_16_13_9_7_1_4532 61 73
  151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 151
  (Polychromatic418967fa.accept_9_6_1_7_1_577 60 73 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 151 (accept_3_3 59 73 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 73 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 151 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 73 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 151 (accept_3_3 56 73 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 151 (Polychromatic418967fa.accept_7_6_3_4_1_294 55 73 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 73 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 151 (accept_3_3 53 73 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 151 (Polychromatic418967fa.accept_10_2_3_1_1_481 52 73 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 151 (Polychromatic418967fa.accept_9_6_1_7_1_577 51 73 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 151 (accept_3_3 50 73 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 73 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 151
  (Polychromatic418967fa.accept_7_6_3_4_1_294 48 73 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 151 (accept_3_3 47 73 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 73 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 151 (Polychromatic418967fa.accept_16_13_9_7_1_4532 45 73 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 151 (accept_3_3 44 73 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 151 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 73 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 73 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 151 (accept_3_3 41 73 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 73 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 151 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 73 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 151 (accept_3_3 38 73 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 151 (Polychromatic418967fa.accept_11_4_7_8_1_1926 37 73 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 151
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 73 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 151 (accept_3_3 35 73 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 73 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 151 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 73 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 151 (accept_3_3 32 73 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 73 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 73 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 151 (accept_3_3 29 73 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 151 (Polychromatic418967fa.accept_10_8_3_1_1_1316 28 73 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 151 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 73 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 151 (accept_3_3 26 73 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 151 (Polychromatic418967fa.accept_15_10_13_1_1_3698 25 73 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 151
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 73 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 151 (accept_3_3 23 73 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 73 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 151 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 73 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 151 (accept_3_3 20 73 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 151 (Polychromatic418967fa.accept_16_3_9_7_1_6842 19 73 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 73 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 151 (accept_3_3 17 73 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 151 (Polychromatic418967fa.accept_18_16_1_7_1_4083 16 73 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 151 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 73 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 151 (accept_3_3 14 73 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 151 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 73 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 151
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 73 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 151 (accept_3_3 11 73 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 73 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 151 (Polychromatic418967fa.accept_19_9_16_18_1_3887 9 73 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 151 (accept_3_3 8 73 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 151 (Polychromatic418967fa.accept_14_7_3_11_1_2199 7 73 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 73 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 151 (accept_3_3 5 73 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  151 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 73 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 151 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 73 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 151 (accept_3_3 2 73 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 151 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 73 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  151))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 151 (allA_succ_of_accept 71
  72 151 (accept_3_3 71 72 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 72 151
  (Polychromatic418967fa.accept_17_2_4_15_1_5451 70 72 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 72 151 (Polychromatic418967fa.accept_7_6_2_4_1_291 69 72 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 72 151 (accept_3_3 68 72 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 72 151 (Polychromatic418967fa.accept_13_2_7_8_1_4221 67 72 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 72 151 (Polychromatic418967fa.accept_10_6_2_1_1_494
  66 72 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 72 151 (accept_3_3 65
  72 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 72 151
  (Polychromatic418967fa.accept_13_12_7_8_1_1104 64 72 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 72 151 (Polychromatic418967fa.accept_10_3_2_1_1_839 63 72 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 72 151 (accept_3_3 62 72 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 72 151 (Polychromatic418967fa.accept_7_5_2_4_1_126 61 72 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 72 151 (Polychromatic418967fa.accept_16_12_8_7_1_4530
  60 72 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 72 151 (accept_3_3 59
  72 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 72 151
  (Polychromatic418967fa.accept_11_3_6_8_1_1924 58 72 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 72 151 (Polychromatic418967fa.accept_16_9_8_7_1_4529 57 72 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 72 151 (accept_3_3 56 72 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 72 151 (Polychromatic418967fa.accept_7_6_2_4_1_291 55 72 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 72 151 (Polychromatic418967fa.accept_7_5_2_4_1_126 54
  72 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 72 151 (accept_3_3 53 72
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 72 151
  (Polychromatic418967fa.accept_16_4_8_7_1_3396 52 72 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 72 151 (Polychromatic418967fa.accept_13_12_7_8_1_1104 51 72 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 72 151 (accept_3_3 50 72 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 72 151 (Polychromatic418967fa.accept_10_9_2_1_1_840 49 72 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 72 151 (Polychromatic418967fa.accept_7_6_2_4_1_291 48
  72 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 72 151 (accept_3_3 47 72
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 72 151
  (Polychromatic418967fa.accept_10_6_2_1_1_494 46 72 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 72 151 (Polychromatic418967fa.accept_17_11_4_15_1_3150 45 72 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 72 151 (accept_3_3 44 72 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 72 151 (Polychromatic418967fa.accept_10_3_2_1_1_839 43 72 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 72 151 (Polychromatic418967fa.accept_13_3_7_8_1_4192
  42 72 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 72 151 (accept_3_3 41
  72 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 72 151
  (Polychromatic418967fa.accept_7_5_2_4_1_126 40 72 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 72 151 (Polychromatic418967fa.accept_10_9_2_1_1_840 39 72 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 72 151 (accept_3_3 38 72 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 72 151 (Polychromatic418967fa.accept_14_9_2_11_1_780 37 72 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 72 151 (Polychromatic418967fa.accept_10_6_2_1_1_494
  36 72 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 72 151 (accept_3_3 35
  72 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 72 151
  (Polychromatic418967fa.accept_7_6_2_4_1_291 34 72 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 72 151 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 72 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 72 151 (accept_3_3 32 72 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 72 151 (Polychromatic418967fa.accept_16_15_8_7_1_3407 31 72 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 72 151
  (Polychromatic418967fa.accept_22_8_6_19_1_8133 30 72 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 72 151 (accept_3_3 29 72 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  72 151 (Polychromatic418967fa.accept_13_2_7_8_1_4221 28 72 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 72 151 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 72 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 72 151 (accept_3_3 26 72 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 151 (Polychromatic418967fa.accept_11_3_6_8_1_1924 25 72 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 72 151
  (Polychromatic418967fa.accept_22_2_6_19_1_6438 24 72 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 72 151 (accept_3_3 23 72 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  72 151 (Polychromatic418967fa.accept_13_9_7_8_1_1122 22 72 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 72 151 (Polychromatic418967fa.accept_19_2_15_18_1_1556 21 72 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 72 151 (accept_3_3 20 72 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 151 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 72 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 72 151
  (Polychromatic418967fa.accept_21_18_9_4_1_4964 18 72 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 72 151 (accept_3_3 17 72 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  72 151 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 72 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 72 151 (Polychromatic418967fa.accept_13_2_7_8_1_4221 15 72 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 72 151 (accept_3_3 14 72 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 151 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 72 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 72 151
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 72 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 72 151 (accept_3_3 11 72 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  72 151 (Polychromatic418967fa.accept_13_10_7_8_1_1794 10 72 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 72 151 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 72 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 72 151 (accept_3_3 8 72 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 151 (Polychromatic418967fa.accept_19_7_15_18_1_8132 7 72 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 72 151
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 72 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 72 151 (accept_3_3 5 72 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 72
  151 (Polychromatic418967fa.accept_15_4_12_1_1_1081 4 72 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 72 151 (Polychromatic418967fa.accept_10_3_2_1_1_839 3 72 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 72 151 (accept_3_3 2 72 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 151 (Polychromatic418967fa.accept_13_1_7_8_1_1796 1 72 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72
  151)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 151 (allA_of_3_1 71 71 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 70 151 (allA_succ_of_accept 69 70 151
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 70 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 70 151 (accept_3_3 68 70 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  70 151 (Polychromatic418967fa.accept_11_1_4_8_1_1918 67 70 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 70 151 (Polychromatic418967fa.accept_13_1_5_8_1_207 66 70 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 70 151 (accept_3_3 65 70 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 70 151 (Polychromatic418967fa.accept_12_4_10_7_1_149 64 70 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 70 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 70 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 70 151 (accept_3_3 62 70 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  70 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 70 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 70 151 (Polychromatic418967fa.accept_21_18_7_4_1_8131 60 70 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 70 151 (accept_3_3 59 70 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 70 151 (Polychromatic418967fa.accept_15_13_10_1_1_1862 58 70
  151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 70 151
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 70 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 70 151 (accept_3_3 56 70 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  70 151 (Polychromatic418967fa.accept_13_3_5_8_1_1099 55 70 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 70 151 (Polychromatic418967fa.accept_15_9_10_1_1_1062 54 70 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 70 151 (accept_3_3 53 70 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 70 151 (Polychromatic418967fa.accept_12_4_10_7_1_149 52 70 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 70 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 70 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 70 151 (accept_3_3 50 70 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  70 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 70 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 70 151 (Polychromatic418967fa.accept_21_6_7_4_1_4993 48 70 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 70 151 (accept_3_3 47 70 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 70 151 (Polychromatic418967fa.accept_19_8_13_18_1_8130 46 70 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 70 151
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 70 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 70 151 (accept_3_3 44 70 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  70 151 (Polychromatic418967fa.accept_15_13_10_1_1_1862 43 70 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 70 151 (Polychromatic418967fa.accept_13_3_5_8_1_1099 42 70 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 70 151 (accept_3_3 41 70 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 70 151 (Polychromatic418967fa.accept_11_7_4_8_1_1371 40 70 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 70 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 70 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 70 151 (accept_3_3 38 70 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  70 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 70 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 70 151 (Polychromatic418967fa.accept_13_10_5_8_1_2555 36 70 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 70 151 (accept_3_3 35 70 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 70 151 (Polychromatic418967fa.accept_11_1_4_8_1_1918 34 70 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 70 151
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 70 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 70 151 (accept_3_3 32 70 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  70 151 (Polychromatic418967fa.accept_16_15_6_7_1_4512 31 70 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 70 151 (Polychromatic418967fa.accept_17_13_2_15_1_2151 30 70 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 70 151 (accept_3_3 29 70 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 70 151 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 70 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 70 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 70 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 70 151 (accept_3_3 26 70 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  70 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 70 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 70 151 (Polychromatic418967fa.accept_15_9_10_1_1_1062 24 70 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 70 151 (accept_3_3 23 70 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 70 151 (Polychromatic418967fa.accept_15_7_10_1_1_1836 22 70
  151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 70 151
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 70 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 70 151 (accept_3_3 20 70 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  70 151 (Polychromatic418967fa.accept_18_1_16_7_1_2897 19 70 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 70 151 (Polychromatic418967fa.accept_11_7_4_8_1_1371 18 70 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 70 151 (accept_3_3 17 70 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 70 151 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 70 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 70 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 70 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 70 151 (accept_3_3 14 70 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  70 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 70 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 70 151 (Polychromatic418967fa.accept_11_1_4_8_1_1918 12 70 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 70 151 (accept_3_3 11 70 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 70 151 (Polychromatic418967fa.accept_13_10_5_8_1_2555 10 70 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 70 151
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 70 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 70 151 (accept_3_3 8 70 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 70
  151 (Polychromatic418967fa.accept_11_7_4_8_1_1371 7 70 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 70 151 (Polychromatic418967fa.accept_15_6_10_1_1_3675 6 70 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 70 151 (accept_3_3 5 70 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 70 151 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 70 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 70 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 70 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 70 151 (accept_3_3 2 70 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 70
  151 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 70 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 70 151)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 151
  (allA_succ_of_accept 68 69 151 (accept_3_3 68 69 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  69 151 (Polychromatic418967fa.accept_9_4_6_7_1_286 67 69 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 69 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 69 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 69 151 (accept_3_3 65 69 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 69 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 151
  (Polychromatic418967fa.accept_12_3_9_7_1_472 63 69 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 69 151 (accept_3_3 62 69 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  69 151 (Polychromatic418967fa.accept_7_5_6_4_1_117 61 69 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 69 151 (Polychromatic418967fa.accept_11_5_3_8_1_454 60 69 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 69 151 (accept_3_3 59 69 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 69 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 151
  (Polychromatic418967fa.accept_9_3_6_7_1_562 57 69 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 69 151 (accept_3_3 56 69 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  69 151 (Polychromatic418967fa.accept_9_1_6_7_1_285 55 69 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 69 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 69 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 69 151 (accept_3_3 53 69 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 69 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 151
  (Polychromatic418967fa.accept_7_2_6_4_1_29 51 69 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 69 151 (accept_3_3 50 69 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  69 151 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 69 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 69 151 (Polychromatic418967fa.accept_9_3_6_7_1_562 48 69 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 69 151 (accept_3_3 47 69 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 69 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 151
  (Polychromatic418967fa.accept_7_3_6_4_1_30 45 69 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 69 151 (accept_3_3 44 69 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  69 151 (Polychromatic418967fa.accept_16_11_5_7_1_2395 43 69 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 69 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 69 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 69 151 (accept_3_3 41 69 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 69 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 151
  (Polychromatic418967fa.accept_9_3_6_7_1_562 39 69 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 69 151 (accept_3_3 38 69 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  69 151 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 69 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 69 151 (Polychromatic418967fa.accept_13_10_4_8_1_2570 36 69 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 69 151 (accept_3_3 35 69 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 69 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 151
  (Polychromatic418967fa.accept_7_5_6_4_1_117 33 69 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 69 151 (accept_3_3 32 69 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  69 151 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 69 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 69 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 69 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 151 (accept_3_3 29 69 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 69 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 151
  (Polychromatic418967fa.accept_11_5_3_8_1_454 27 69 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 69 151 (accept_3_3 26 69 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  69 151 (Polychromatic418967fa.accept_10_5_9_1_1_187 25 69 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 69 151 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 69 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 151 (accept_3_3 23 69 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 69 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 151
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 69 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 69 151 (accept_3_3 20 69 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  69 151 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 69 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 69 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 69 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 151 (accept_3_3 17 69 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 69 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 151
  (Polychromatic418967fa.accept_10_5_9_1_1_187 15 69 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 69 151 (accept_3_3 14 69 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  69 151 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 69 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 69 151 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 69 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 151 (accept_3_3 11 69 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 69 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 151
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 69 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 69 151 (accept_3_3 8 69 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69
  151 (Polychromatic418967fa.accept_15_7_9_1_1_473 7 69 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 69 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 69 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 151 (accept_3_3 5 69 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 69 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 69 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 151 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 69
  151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 151 (accept_3_3 2 69 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 151 (Polychromatic418967fa.accept_9_1_6_7_1_285 1
  69 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  151))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 151 (allA_of_3_1 68 68 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 67 151 (allA_succ_of_accept 66 67 151
  (Polychromatic418967fa.accept_9_3_4_7_1_89 66 67 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 151 (accept_3_3 65 67 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 67 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 151 (Polychromatic418967fa.accept_16_15_3_7_1_3389 63 67 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 151 (accept_3_3 62 67 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 151 (Polychromatic418967fa.accept_20_1_7_11_1_3673 61 67
  151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 151
  (Polychromatic418967fa.accept_8_4_3_7_1_491 60 67 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 151 (accept_3_3 59 67 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 151 (Polychromatic418967fa.accept_13_6_2_8_1_1782 58 67 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 151 (Polychromatic418967fa.accept_9_3_4_7_1_89 57 67 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 151 (accept_3_3 56 67 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 67 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 151
  (Polychromatic418967fa.accept_10_4_7_1_1_471 54 67 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 151 (accept_3_3 53 67 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 151 (Polychromatic418967fa.accept_8_4_3_7_1_491 52 67 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 151 (Polychromatic418967fa.accept_9_6_4_7_1_300 51 67 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 151 (accept_3_3 50 67 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 151 (Polychromatic418967fa.accept_13_10_2_8_1_2603 49 67 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 151
  (Polychromatic418967fa.accept_9_3_4_7_1_89 48 67 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 151 (accept_3_3 47 67 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 67 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 151 (Polychromatic418967fa.accept_13_6_2_8_1_1782 45 67 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 151 (accept_3_3 44 67 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 151 (Polychromatic418967fa.accept_16_11_3_7_1_2375 43 67 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 151
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 67 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 151 (accept_3_3 41 67 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 151 (Polychromatic418967fa.accept_15_10_7_1_1_3686 40 67 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 151 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 67 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 151 (accept_3_3 38 67 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 67 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 151
  (Polychromatic418967fa.accept_8_4_3_7_1_491 36 67 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 151 (accept_3_3 35 67 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 151 (Polychromatic418967fa.accept_10_4_7_1_1_471 34 67 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 151 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 67 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 151 (accept_3_3 32 67 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 151 (Polychromatic418967fa.accept_16_15_3_7_1_3389 31 67 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 151
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 67 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 151 (accept_3_3 29 67 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 151 (Polychromatic418967fa.accept_8_4_3_7_1_491 28 67 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 151 (Polychromatic418967fa.accept_16_11_3_7_1_2375 27 67 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 151 (accept_3_3 26 67 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 151 (Polychromatic418967fa.accept_15_10_7_1_1_3686 25 67
  151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 151
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 67 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 151 (accept_3_3 23 67 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 151 (Polychromatic418967fa.accept_18_4_13_7_1_5395 22 67 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 151 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 67 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 151 (accept_3_3 20 67 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 67 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 151
  (Polychromatic418967fa.accept_17_1_16_15_1_4315 18 67 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 151 (accept_3_3 17 67 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 151 (Polychromatic418967fa.accept_10_6_7_1_1_1297 16 67 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 151 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 67 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 151 (accept_3_3 14 67 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 151 (Polychromatic418967fa.accept_24_13_19_7_1_8129 13 67 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 151
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 67 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 151 (accept_3_3 11 67 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 67 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 151 (Polychromatic418967fa.accept_15_9_7_1_1_1075 9 67 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 151 (accept_3_3 8 67 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 151 (Polychromatic418967fa.accept_13_7_2_8_1_1746 7 67 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 151
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 67 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 151 (accept_3_3 5 67 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  151 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 67 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 67 151 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 67 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 151 (accept_3_3 2 67 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 67 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 67 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  151))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 151 (allA_succ_of_accept 65 66
  151 (accept_3_3 65 66 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 66 151
  (Polychromatic418967fa.accept_7_1_3_4_1_128 64 66 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 66 151 (Polychromatic418967fa.accept_13_11_1_8_1_1776 63 66 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 66 151 (accept_3_3 62 66 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 66 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 66 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 66 151 (Polychromatic418967fa.accept_9_6_3_7_1_580 60
  66 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 66 151 (accept_3_3 59 66
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 66 151
  (Polychromatic418967fa.accept_9_4_3_7_1_296 58 66 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 66 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 66 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 66 151 (accept_3_3 56 66 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 66 151 (Polychromatic418967fa.accept_7_6_3_4_1_294 55 66 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 66 151 (Polychromatic418967fa.accept_15_9_6_1_1_493
  54 66 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 66 151 (accept_3_3 53
  66 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 66 151
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 52 66 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 66 151 (Polychromatic418967fa.accept_9_6_3_7_1_580 51 66 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 66 151 (accept_3_3 50 66 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 66 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 66 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 66 151 (Polychromatic418967fa.accept_7_6_3_4_1_294 48
  66 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 66 151 (accept_3_3 47 66
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 66 151 (Polychromatic418967fa.accept_9_1_3_7_1_6
  46 66 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 66 151
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 66 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 66 151 (accept_3_3 44 66 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  66 151 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 66 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 66 151 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 66 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 66 151 (accept_3_3 41 66 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 66 151 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 66 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 66 151
  (Polychromatic418967fa.accept_15_9_6_1_1_493 39 66 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 66 151 (accept_3_3 38 66 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  66 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 66 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 66 151 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 66 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 66 151 (accept_3_3 35 66 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 66 151 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 66 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 66 151
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 66 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 66 151 (accept_3_3 32 66 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  66 151 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 66 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 66 151 (Polychromatic418967fa.accept_23_7_20_13_1_8128 30 66 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 66 151 (accept_3_3 29 66 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 66 151 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 66 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 66 151
  (Polychromatic418967fa.accept_7_6_3_4_1_294 27 66 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 66 151 (accept_3_3 26 66 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  66 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 66 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 66 151 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 66 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 66 151 (accept_3_3 23 66 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 66 151 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 66 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 66 151
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 66 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 66 151 (accept_3_3 20 66 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  66 151 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 66 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 66 151 (Polychromatic418967fa.accept_13_5_1_8_1_1115 18 66 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 66 151 (accept_3_3 17 66 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 66 151 (Polychromatic418967fa.accept_19_16_9_18_1_8127 16 66 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 66 151
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 66 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 66 151 (accept_3_3 14 66 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  66 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 66 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 66 151 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 66 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 66 151 (accept_3_3 11 66 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 66 151 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 66 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 66 151
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 66 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 66 151 (accept_3_3 8 66 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66
  151 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 66 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 66 151 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 66 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 66 151 (accept_3_3 5 66 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 66 151 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 66 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 66 151 (Polychromatic418967fa.accept_15_3_6_1_1_1834 3
  66 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 66 151 (accept_3_3 2 66 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 66
  151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  151)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 151 (allA_of_3_1 65 65 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 64 151 (allA_succ_of_accept 63 64 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 64 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 64 151 (accept_3_3 62 64 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  64 151 (Polychromatic418967fa.accept_7_5_1_4_1_122 61 64 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 64 151 (Polychromatic418967fa.accept_9_6_1_7_1_577 60 64 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 64 151 (accept_3_3 59 64 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 64 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 58 64 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 64 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 64 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 64 151 (accept_3_3 56 64 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  64 151 (Polychromatic418967fa.accept_10_5_4_1_1_842 55 64 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 64 151 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 64 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 64 151 (accept_3_3 53 64 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 64 151 (Polychromatic418967fa.accept_7_3_1_4_1_121 52 64 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 64 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 64 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 64 151 (accept_3_3 50 64 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  64 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 64 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 64 151 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 64 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 64 151 (accept_3_3 47 64 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 64 151 (Polychromatic418967fa.accept_12_10_4_7_1_948 46 64 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 64 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 64 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 64 151 (accept_3_3 44 64 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  64 151 (Polychromatic418967fa.accept_11_10_9_8_1_1974 43 64 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 64 151 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 64 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 64 151 (accept_3_3 41 64 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 64 151 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 64 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 64 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 64 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 64 151 (accept_3_3 38 64 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  64 151 (Polychromatic418967fa.accept_10_7_4_1_1_1319 37 64 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 64 151 (Polychromatic418967fa.accept_13_10_12_8_1_2550 36 64 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 64 151 (accept_3_3 35 64 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 64 151 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 64 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 64 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 64 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 64 151 (accept_3_3 32 64 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  64 151 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 64 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 64 151 (Polychromatic418967fa.accept_9_3_1_7_1_97 30 64 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 64 151 (accept_3_3 29 64 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 64 151 (Polychromatic418967fa.accept_17_11_13_15_1_2140 28 64 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 64 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 64 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 64 151 (accept_3_3 26 64 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  64 151 (Polychromatic418967fa.accept_10_5_4_1_1_842 25 64 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 64 151 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 64 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 64 151 (accept_3_3 23 64 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 64 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 64 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 64 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 64 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 64 151 (accept_3_3 20 64 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  64 151 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 64 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 64 151 (Polychromatic418967fa.accept_13_5_12_8_1_198 18 64 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 64 151 (accept_3_3 17 64 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 64 151 (Polychromatic418967fa.accept_23_16_18_13_1_8126 16 64 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 64 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 64 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 64 151 (accept_3_3 14 64 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  64 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 64 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 64 151 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 64 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 64 151 (accept_3_3 11 64 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 64 151 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 64 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 64 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 64 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 64 151 (accept_3_3 8 64 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 64
  151 (Polychromatic418967fa.accept_10_7_4_1_1_1319 7 64 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 64 151 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 64 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 64 151 (accept_3_3 5 64 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 64 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 64 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 64 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 64 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 64 151 (accept_3_3 2 64 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 64
  151 (Polychromatic418967fa.accept_13_1_12_8_1_1818 1 64 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 64 151)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 151
  (allA_succ_of_accept 62 63 151 (accept_3_3 62 63 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  63 151 (Polychromatic418967fa.accept_13_9_11_8_1_195 61 63 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 63 151 (Polychromatic418967fa.accept_14_4_7_11_1_790 60 63 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 63 151 (accept_3_3 59 63 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 63 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 151
  (Polychromatic418967fa.accept_12_9_3_7_1_924 57 63 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 63 151 (accept_3_3 56 63 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  63 151 (Polychromatic418967fa.accept_13_3_11_8_1_1094 55 63 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 63 151 (Polychromatic418967fa.accept_16_6_15_7_1_1510 54 63 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 63 151 (accept_3_3 53 63 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 63 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 151
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 51 63 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 63 151 (accept_3_3 50 63 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  63 151 (Polychromatic418967fa.accept_13_10_11_8_1_1770 49 63 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 63 151 (Polychromatic418967fa.accept_10_8_3_1_1_1316 48 63 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 63 151 (accept_3_3 47 63 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 63 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 151
  (Polychromatic418967fa.accept_12_9_3_7_1_924 45 63 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 63 151 (accept_3_3 44 63 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  63 151 (Polychromatic418967fa.accept_13_4_11_8_1_1768 43 63 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 63 151 (Polychromatic418967fa.accept_10_2_3_1_1_481 42 63 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 63 151 (accept_3_3 41 63 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 63 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 151
  (Polychromatic418967fa.accept_18_3_9_7_1_1839 39 63 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 63 151 (accept_3_3 38 63 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  63 151 (Polychromatic418967fa.accept_17_3_12_15_1_1203 37 63 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 63 151 (Polychromatic418967fa.accept_13_10_11_8_1_1770 36 63 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 63 151 (accept_3_3 35 63 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 63 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 151
  (Polychromatic418967fa.accept_12_9_3_7_1_924 33 63 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 63 151 (accept_3_3 32 63 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  63 151 (Polychromatic418967fa.accept_14_3_7_11_1_765 31 63 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 63 151 (Polychromatic418967fa.accept_13_4_11_8_1_1768 30 63 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 151 (accept_3_3 29 63 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 63 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 151
  (Polychromatic418967fa.accept_13_1_11_8_1_2562 27 63 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 63 151 (accept_3_3 26 63 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  63 151 (Polychromatic418967fa.accept_27_25_9_16_1_8125 25 63 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 63 151 (Polychromatic418967fa.accept_14_10_7_11_1_3015 24 63 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 151 (accept_3_3 23 63 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 63 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 151
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 63 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 63 151 (accept_3_3 20 63 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  63 151 (Polychromatic418967fa.accept_13_6_11_8_1_1111 19 63 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 63 151 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 63 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 151 (accept_3_3 17 63 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 63 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 151
  (Polychromatic418967fa.accept_26_15_11_21_1_8124 15 63 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 63 151 (accept_3_3 14 63 151 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 151 (Polychromatic418967fa.accept_15_13_3_1_1_3740 13 63 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 63 151 (Polychromatic418967fa.accept_10_2_3_1_1_481 12 63 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 151 (accept_3_3 11 63 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 10
  63 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 151
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 63 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 63 151 (accept_3_3 8 63 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63
  151 (Polychromatic418967fa.accept_19_7_6_18_1_8123 7 63 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 63 151 (Polychromatic418967fa.accept_13_6_11_8_1_1111 6 63 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 151 (accept_3_3 5 63 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 63 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 151
  (Polychromatic418967fa.accept_13_3_11_8_1_1094 3 63 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 63 151 (accept_3_3 2 63 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63
  151 (Polychromatic418967fa.accept_13_1_11_8_1_2562 1 63 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 63 151))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 151
  (allA_of_3_1 62 62 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 61 151 (allA_succ_of_accept 60 61 151
  (Polychromatic418967fa.accept_19_3_4_18_1_3882 60 61 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 151 (accept_3_3 59 61 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 61 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 151 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 61 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 151 (accept_3_3 56 61 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 151 (Polychromatic418967fa.accept_7_6_5_4_1_297 55 61 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 61 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 151 (accept_3_3 53 61 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 151 (Polychromatic418967fa.accept_16_4_13_7_1_4522 52 61 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 151 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 61 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 151 (accept_3_3 50 61 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 151 (Polychromatic418967fa.accept_19_11_4_18_1_5226 49 61 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 151
  (Polychromatic418967fa.accept_7_6_5_4_1_297 48 61 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 151 (accept_3_3 47 61 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 61 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 151 (Polychromatic418967fa.accept_24_21_13_7_1_8122 45 61 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 151 (accept_3_3 44 61 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 151 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 61 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 61 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 151 (accept_3_3 41 61 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 151 (Polychromatic418967fa.accept_13_1_9_8_1_1734 40 61 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 151 (Polychromatic418967fa.accept_17_5_10_15_1_5574 39 61 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 151 (accept_3_3 38 61 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 151 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 61 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 151
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 61 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 151 (accept_3_3 35 61 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 61 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 151 (Polychromatic418967fa.accept_13_7_9_8_1_188 33 61 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 151 (accept_3_3 32 61 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 151 (Polychromatic418967fa.accept_21_10_19_4_1_8121 31 61 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 61 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 151 (accept_3_3 29 61 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 151 (Polychromatic418967fa.accept_20_8_1_11_1_5125 28 61 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 151 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 61 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 151 (accept_3_3 26 61 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 151 (Polychromatic418967fa.accept_11_3_6_8_1_1924 25 61 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 151
  (Polychromatic418967fa.accept_13_11_9_8_1_1125 24 61 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 151 (accept_3_3 23 61 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 61 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 151 (Polychromatic418967fa.accept_17_4_10_15_1_5444 21 61 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 151 (accept_3_3 20 61 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 151 (Polychromatic418967fa.accept_17_2_10_15_1_1238 19 61
  151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 61 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 151 (accept_3_3 17 61 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 151 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 61 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 151 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 61 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 151 (accept_3_3 14 61 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 151 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 61 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 151
  (Polychromatic418967fa.accept_13_12_9_8_1_2595 12 61 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 151 (accept_3_3 11 61 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 61 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 151 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 61 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 151 (accept_3_3 8 61 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 151 (Polychromatic418967fa.accept_13_7_9_8_1_188 7 61 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 61 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 151 (accept_3_3 5 61 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  151 (Polychromatic418967fa.accept_13_4_9_8_1_1736 4 61 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 61 151 (Polychromatic418967fa.accept_11_3_6_8_1_1924 3 61 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 151 (accept_3_3 2 61 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 61 151 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 61 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61
  151))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 60 151 (allA_succ_of_accept 59 60 151
  (accept_3_3 59 60 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 60 151
  (Polychromatic418967fa.accept_9_4_6_7_1_286 58 60 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 60 151 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 60 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 60 151 (accept_3_3 56 60 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 60 151 (Polychromatic418967fa.accept_9_1_6_7_1_285 55 60 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 60 151
  (Polychromatic418967fa.accept_19_16_3_18_1_8120 54 60 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 60 151 (accept_3_3 53 60 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  60 151 (Polychromatic418967fa.accept_16_4_12_7_1_4475 52 60 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 60 151 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 60 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 60 151 (accept_3_3 50 60 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 60 151 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 60 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 60 151
  (Polychromatic418967fa.accept_9_3_6_7_1_562 48 60 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 60 151 (accept_3_3 47 60 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  60 151 (Polychromatic418967fa.accept_9_1_6_7_1_285 46 60 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 60 151 (Polychromatic418967fa.accept_18_9_6_7_1_6719 45 60 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 60 151 (accept_3_3 44 60 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 151 (Polychromatic418967fa.accept_8_3_4_7_1_475 43 60 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 60 151
  (Polychromatic418967fa.accept_19_4_3_18_1_2699 42 60 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 60 151 (accept_3_3 41 60 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  60 151 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 60 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 60 151 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 60 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 60 151 (accept_3_3 38 60 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 151 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 60 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 60 151
  (Polychromatic418967fa.accept_11_3_5_8_1_458 36 60 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 60 151 (accept_3_3 35 60 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  60 151 (Polychromatic418967fa.accept_16_2_12_7_1_3410 34 60 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 60 151 (Polychromatic418967fa.accept_19_14_3_18_1_6675 33 60 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 60 151 (accept_3_3 32 60 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 151 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 60 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 60 151
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 60 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 60 151 (accept_3_3 29 60 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  60 151 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 60 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 60 151 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 60 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 60 151 (accept_3_3 26 60 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 60 151 (Polychromatic418967fa.accept_11_3_5_8_1_458 25 60 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 60 151
  (Polychromatic418967fa.accept_11_2_5_8_1_470 24 60 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 60 151 (accept_3_3 23 60 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  60 151 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 60 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 60 151 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 60 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 60 151 (accept_3_3 20 60 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 151 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 60 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 60 151
  (Polychromatic418967fa.accept_16_2_12_7_1_3410 18 60 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 60 151 (accept_3_3 17 60 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  60 151 (Polychromatic418967fa.accept_19_16_3_18_1_8120 16 60 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 60 151 (Polychromatic418967fa.accept_14_1_4_11_1_3036 15 60 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 60 151 (accept_3_3 14 60 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 151 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 60 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 60 151
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 60 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 60 151 (accept_3_3 11 60 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  60 151 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 60 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 60 151 (Polychromatic418967fa.accept_18_9_6_7_1_6719 9 60 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 60 151 (accept_3_3 8 60 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 151 (Polychromatic418967fa.accept_14_7_4_11_1_3038 7 60 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 60 151
  (Polychromatic418967fa.accept_17_6_9_15_1_3185 6 60 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 60 151 (accept_3_3 5 60 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 60
  151 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 60 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 60 151 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 60 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 60 151 (accept_3_3 2 60 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 60 151 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 60 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60 151))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 59 151 (allA_of_3_1 59 59 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 58 151
  (allA_succ_of_accept 57 58 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 58 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 58 151 (accept_3_3 56 58 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 58 151 (Polychromatic418967fa.accept_7_6_2_4_1_291 55 58 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 58 151 (Polychromatic418967fa.accept_7_5_2_4_1_126 54
  58 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 58 151 (accept_3_3 53 58
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 58 151
  (Polychromatic418967fa.accept_12_4_10_7_1_149 52 58 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 58 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 58 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 58 151 (accept_3_3 50 58 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 58 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 58 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 58 151 (Polychromatic418967fa.accept_7_6_2_4_1_291 48
  58 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 58 151 (accept_3_3 47 58
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 58 151 (Polychromatic418967fa.accept_9_1_4_7_1_7
  46 58 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 58 151
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 58 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 58 151 (accept_3_3 44 58 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  58 151 (Polychromatic418967fa.accept_10_3_8_1_1_182 43 58 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 58 151 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 58 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 58 151 (accept_3_3 41 58 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 58 151 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 58 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 58 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 58 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 58 151 (accept_3_3 38 58 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  58 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 58 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 58 151 (Polychromatic418967fa.accept_17_2_7_15_1_5525 36 58 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 58 151 (accept_3_3 35 58 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 58 151 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 58 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 58 151
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 58 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 58 151 (accept_3_3 32 58 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  58 151 (Polychromatic418967fa.accept_18_13_4_7_1_4086 31 58 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 58 151 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 58 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 58 151 (accept_3_3 29 58 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 58 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 58 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 58 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 58 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 58 151 (accept_3_3 26 58 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  58 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 58 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 58 151 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 58 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 58 151 (accept_3_3 23 58 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 58 151 (Polychromatic418967fa.accept_17_5_7_15_1_1230 22 58 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 58 151
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 58 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 58 151 (accept_3_3 20 58 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  58 151 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 58 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 58 151 (Polychromatic418967fa.accept_15_3_13_1_1_479 18 58 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 58 151 (accept_3_3 17 58 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 58 151 (Polychromatic418967fa.accept_11_5_3_8_1_454 16 58 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 58 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 58 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 58 151 (accept_3_3 14 58 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  58 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 58 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 58 151 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 58 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 58 151 (accept_3_3 11 58 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 58 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 58 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 58 151
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 58 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 58 151 (accept_3_3 8 58 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 58
  151 (Polychromatic418967fa.accept_19_7_1_18_1_2691 7 58 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 58 151 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 58 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 58 151 (accept_3_3 5 58 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 58 151 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 58 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 58 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 58 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 58 151 (accept_3_3 2 58 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 58
  151 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 58 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 58 151)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 151 (allA_succ_of_accept 56
  57 151 (accept_3_3 56 57 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 151
  (Polychromatic418967fa.accept_9_1_3_7_1_6 55 57 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 57 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 57 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 151 (accept_3_3 53 57 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 57 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 57 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 151 (Polychromatic418967fa.accept_9_6_3_7_1_580 51
  57 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 151 (accept_3_3 50 57
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 151
  (Polychromatic418967fa.accept_9_4_3_7_1_296 49 57 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 57 151 (Polychromatic418967fa.accept_17_14_6_15_1_3151 48 57 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 57 151 (accept_3_3 47 57 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 57 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 57 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 151 (Polychromatic418967fa.accept_7_3_1_4_1_121 45
  57 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 151 (accept_3_3 44 57
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 151
  (Polychromatic418967fa.accept_15_13_12_1_1_1841 43 57 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 57 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 57 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 57 151 (accept_3_3 41 57 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 57 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 57 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 151 (Polychromatic418967fa.accept_12_3_9_7_1_472
  39 57 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 151 (accept_3_3 38
  57 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 151
  (Polychromatic418967fa.accept_9_1_3_7_1_6 37 57 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 57 151 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 57 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 57 151 (accept_3_3 35 57 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 57 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 57 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 151 (Polychromatic418967fa.accept_7_5_1_4_1_122 33
  57 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 151 (accept_3_3 32 57
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 151
  (Polychromatic418967fa.accept_7_3_1_4_1_121 31 57 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 57 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 57 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 57 151 (accept_3_3 29 57 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 57 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 57 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 151 (Polychromatic418967fa.accept_11_5_2_8_1_866
  27 57 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 151 (accept_3_3 26
  57 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 151
  (Polychromatic418967fa.accept_13_12_5_8_1_1101 25 57 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 57 151 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 57 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 57 151 (accept_3_3 23 57 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 57 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 57 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 151
  (Polychromatic418967fa.accept_20_1_17_11_1_8119 21 57 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 57 151 (accept_3_3 20 57 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  57 151 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 57 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 57 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 57 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 57 151 (accept_3_3 17 57 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 57 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 151
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 57 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 57 151 (accept_3_3 14 57 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  57 151 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 57 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 57 151 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 57 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 57 151 (accept_3_3 11 57 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 57 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 151
  (Polychromatic418967fa.accept_17_9_6_15_1_5454 9 57 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 57 151 (accept_3_3 8 57 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57
  151 (Polychromatic418967fa.accept_22_7_13_19_1_8118 7 57 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 57 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 57 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 57 151 (accept_3_3 5 57 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 57 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 57 151
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 57 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 57 151 (accept_3_3 2 57 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57
  151 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 57 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 57 151))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 56 151 (allA_of_3_1 56 56 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 55 151 (allA_succ_of_accept 54 55 151
  (Polychromatic418967fa.accept_7_5_6_4_1_117 54 55 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 55 151 (accept_3_3 53 55 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  55 151 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 55 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 55 151 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 55 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 55 151 (accept_3_3 50 55 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 55 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 55 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 55 151
  (Polychromatic418967fa.accept_9_3_1_7_1_97 48 55 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 55 151 (accept_3_3 47 55 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  55 151 (Polychromatic418967fa.accept_10_6_5_1_1_482 46 55 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 55 151 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 55 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 55 151 (accept_3_3 44 55 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 151 (Polychromatic418967fa.accept_15_13_10_1_1_1862 43 55 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 151
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 55 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 151 (accept_3_3 41 55 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  55 151 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 55 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 55 151 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 55 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 55 151 (accept_3_3 38 55 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 55 151 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 55 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 151
  (Polychromatic418967fa.accept_10_6_5_1_1_482 36 55 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 55 151 (accept_3_3 35 55 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  55 151 (Polychromatic418967fa.accept_10_4_5_1_1_497 34 55 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 55 151 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 55 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 151 (accept_3_3 32 55 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 55 151 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 55 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 55 151
  (Polychromatic418967fa.accept_7_2_6_4_1_29 30 55 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 55 151 (accept_3_3 29 55 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  55 151 (Polychromatic418967fa.accept_15_13_10_1_1_1862 28 55 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 55 151 (Polychromatic418967fa.accept_17_10_4_15_1_2165 27 55 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 151 (accept_3_3 26 55 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 55 151 (Polychromatic418967fa.accept_19_6_17_18_1_8117 25 55
  151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 55 151
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 55 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 55 151 (accept_3_3 23 55 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  55 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 55 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 55 151 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 55 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 55 151 (accept_3_3 20 55 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 55 151 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 55 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 151
  (Polychromatic418967fa.accept_13_5_3_8_1_1117 18 55 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 55 151 (accept_3_3 17 55 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  55 151 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 55 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 55 151 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 55 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 55 151 (accept_3_3 14 55 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 55 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 151
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 55 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 151 (accept_3_3 11 55 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  55 151 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 55 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 55 151 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 55 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 151 (accept_3_3 8 55 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 151 (Polychromatic418967fa.accept_13_7_3_8_1_1750 7 55 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 151
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 55 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 55 151 (accept_3_3 5 55 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 55
  151 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 55 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 151 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 55 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 151 (accept_3_3 2 55 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 151 (Polychromatic418967fa.accept_19_1_17_18_1_8101 1 55 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 151)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 54 151 (allA_succ_of_accept 53 54 151 (accept_3_3 53 54 151 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 54 151 (Polychromatic418967fa.accept_15_7_9_1_1_473 52 54 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 54 151 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 54 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 54 151 (accept_3_3 50 54 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 49
  54 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 151
  (Polychromatic418967fa.accept_7_6_5_4_1_297 48 54 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 54 151 (accept_3_3 47 54 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  54 151 (Polychromatic418967fa.accept_13_7_2_8_1_1746 46 54 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 54 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 54 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 54 151 (accept_3_3 44 54 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 151 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 54 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 151
  (Polychromatic418967fa.accept_11_9_10_8_1_444 42 54 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 54 151 (accept_3_3 41 54 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  54 151 (Polychromatic418967fa.accept_15_10_9_1_1_3688 40 54 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 54 151 (Polychromatic418967fa.accept_21_18_12_4_1_4967 39 54 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 54 151 (accept_3_3 38 54 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 54 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 54 151
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 54 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 54 151 (accept_3_3 35 54 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  54 151 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 54 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 54 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 54 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 54 151 (accept_3_3 32 54 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 151 (Polychromatic418967fa.accept_11_9_10_8_1_444 31 54 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 54 151
  (Polychromatic418967fa.accept_7_2_5_4_1_115 30 54 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 54 151 (accept_3_3 29 54 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  54 151 (Polychromatic418967fa.accept_19_9_16_18_1_3887 28 54 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 54 151 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 54 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 151 (accept_3_3 26 54 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 54 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 54 151
  (Polychromatic418967fa.accept_21_3_12_4_1_8116 24 54 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 54 151 (accept_3_3 23 54 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  54 151 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 54 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 54 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 54 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 151 (accept_3_3 20 54 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 151 (Polychromatic418967fa.accept_13_6_2_8_1_1782 19 54 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 54 151
  (Polychromatic418967fa.accept_17_1_3_15_1_2153 18 54 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 54 151 (accept_3_3 17 54 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  54 151 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 54 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 54 151 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 54 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 151 (accept_3_3 14 54 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 54 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 54 151
  (Polychromatic418967fa.accept_17_12_3_15_1_5476 12 54 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 54 151 (accept_3_3 11 54 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  54 151 (Polychromatic418967fa.accept_13_10_2_8_1_2603 10 54 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 54 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 54 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 151 (accept_3_3 8 54 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 151 (Polychromatic418967fa.accept_10_7_4_1_1_1319 7 54 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54 151
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 54 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 54 151 (accept_3_3 5 54 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54
  151 (Polychromatic418967fa.accept_23_4_8_13_1_8115 4 54 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 54 151 (Polychromatic418967fa.accept_19_3_16_18_1_2683 3 54 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 151 (accept_3_3 2 54 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 54 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  151)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 151 (allA_of_3_1 53 53 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 52 151 (allA_succ_of_accept 51 52 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 52
  151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 52 151 (accept_3_3 50 52 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 52 151 (Polychromatic418967fa.accept_10_9_2_1_1_840
  49 52 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 151
  (Polychromatic418967fa.accept_7_6_3_4_1_294 48 52 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 52 151 (accept_3_3 47 52 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  52 151 (Polychromatic418967fa.accept_10_6_2_1_1_494 46 52 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 52 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 52 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 52 151 (accept_3_3 44 52 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 52 151 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 52 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 52 151
  (Polychromatic418967fa.accept_19_4_14_18_1_5234 42 52 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 52 151 (accept_3_3 41 52 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  52 151 (Polychromatic418967fa.accept_15_10_7_1_1_3686 40 52 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 52 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 52 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 52 151 (accept_3_3 38 52 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 52 151 (Polychromatic418967fa.accept_17_3_1_15_1_6835 37 52 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 52 151
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 52 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 52 151 (accept_3_3 35 52 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  52 151 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 52 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 52 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 52 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 52 151 (accept_3_3 32 52 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 52 151 (Polychromatic418967fa.accept_22_9_8_19_1_8114 31 52 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 52 151
  (Polychromatic418967fa.accept_16_14_4_7_1_2380 30 52 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 52 151 (accept_3_3 29 52 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  52 151 (Polychromatic418967fa.accept_16_12_4_7_1_3391 28 52 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 52 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 52 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 52 151 (accept_3_3 26 52 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 52 151 (Polychromatic418967fa.accept_15_10_7_1_1_3686 25 52 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 52 151
  (Polychromatic418967fa.accept_15_9_7_1_1_1075 24 52 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 52 151 (accept_3_3 23 52 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  52 151 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 52 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 52 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 52 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 52 151 (accept_3_3 20 52 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 52 151 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 52 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 52 151
  (Polychromatic418967fa.accept_22_18_8_19_1_8113 18 52 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 52 151 (accept_3_3 17 52 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  52 151 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 52 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 52 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 52 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 52 151 (accept_3_3 14 52 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 52 151 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 52 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 52 151
  (Polychromatic418967fa.accept_16_12_4_7_1_3391 12 52 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 52 151 (accept_3_3 11 52 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  52 151 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 52 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 52 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 52 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 52 151 (accept_3_3 8 52 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 52 151 (Polychromatic418967fa.accept_14_7_10_11_1_8112 7 52 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 52 151
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 52 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 52 151 (accept_3_3 5 52 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 52
  151 (Polychromatic418967fa.accept_18_4_16_7_1_1873 4 52 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 52 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 52 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 52 151 (accept_3_3 2 52 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 52 151 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 52 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52
  151)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 151 (allA_succ_of_accept 50 51 151 (accept_3_3
  50 51 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 151
  (Polychromatic418967fa.accept_9_4_6_7_1_286 49 51 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 51 151 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 51 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 151 (accept_3_3 47 51 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 51 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 51 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 151 (Polychromatic418967fa.accept_12_9_3_7_1_924
  45 51 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 151 (accept_3_3 44
  51 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 151
  (Polychromatic418967fa.accept_13_4_12_8_1_197 43 51 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 51 151 (Polychromatic418967fa.accept_16_10_3_7_1_8094 42 51 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 151 (accept_3_3 41 51 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 51 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 51 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 151 (Polychromatic418967fa.accept_9_3_6_7_1_562 39
  51 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 151 (accept_3_3 38 51
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 151
  (Polychromatic418967fa.accept_9_1_6_7_1_285 37 51 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 51 151 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 51 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 51 151 (accept_3_3 35 51 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 51 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 51 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 151 (Polychromatic418967fa.accept_7_5_2_4_1_126 33
  51 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 151 (accept_3_3 32 51
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 151
  (Polychromatic418967fa.accept_9_4_6_7_1_286 31 51 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 51 151 (Polychromatic418967fa.accept_9_3_6_7_1_562 30 51 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 151 (accept_3_3 29 51 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 51 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 51 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 151 (Polychromatic418967fa.accept_7_6_2_4_1_291 27
  51 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 151 (accept_3_3 26 51
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 151
  (Polychromatic418967fa.accept_15_10_6_1_1_3707 25 51 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 51 151 (Polychromatic418967fa.accept_15_9_6_1_1_493 24 51 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 51 151 (accept_3_3 23 51 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 51 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 51 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 151 (Polychromatic418967fa.accept_9_3_6_7_1_562 21
  51 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 151 (accept_3_3 20 51
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 151
  (Polychromatic418967fa.accept_7_5_2_4_1_126 19 51 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 51 151 (Polychromatic418967fa.accept_13_5_12_8_1_198 18 51 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 51 151 (accept_3_3 17 51 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 51 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 51 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 151 (Polychromatic418967fa.accept_11_4_7_8_1_1926
  15 51 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 151 (accept_3_3 14
  51 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 151
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 51 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 51 151 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 51 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 151 (accept_3_3 11 51 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 51 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 51 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 151 (Polychromatic418967fa.accept_12_9_3_7_1_924 9
  51 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 151 (accept_3_3 8 51 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 151 (Polychromatic418967fa.accept_13_7_12_8_1_199 7
  51 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51 151
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 51 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 151 (accept_3_3 5 51 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51
  151 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 51 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 51 151 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 51 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 151 (accept_3_3 2 51 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 51 151 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 51 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 151)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 151 (allA_of_3_1 50 50 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 49 151
  (allA_succ_of_accept 48 49 151 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 49 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 151 (accept_3_3 47 49 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 49 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 49 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 151 (Polychromatic418967fa.accept_10_5_9_1_1_187
  45 49 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 151 (accept_3_3 44
  49 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 151
  (Polychromatic418967fa.accept_13_4_10_8_1_1817 43 49 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 49 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 49 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 49 151 (accept_3_3 41 49 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 49 151 (Polychromatic418967fa.accept_16_8_1_7_1_2355 40 49 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 151 (Polychromatic418967fa.accept_9_3_4_7_1_89 39
  49 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 151 (accept_3_3 38 49
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 49 151 (Polychromatic418967fa.accept_9_1_4_7_1_7
  37 49 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 151
  (Polychromatic418967fa.accept_11_3_5_8_1_458 36 49 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 49 151 (accept_3_3 35 49 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  49 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 49 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 49 151 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 49 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 151 (accept_3_3 32 49 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 151 (Polychromatic418967fa.accept_13_5_10_8_1_1127 31 49 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 49 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 49 151 (accept_3_3 29 49 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  49 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 49 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 49 151 (Polychromatic418967fa.accept_15_12_4_1_1_3746 27 49 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 49 151 (accept_3_3 26 49 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 49 151 (Polychromatic418967fa.accept_10_5_9_1_1_187 25 49 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 151
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 49 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 49 151 (accept_3_3 23 49 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  49 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 49 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 49 151 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 49 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 49 151 (accept_3_3 20 49 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 49 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 49 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 49 151 (accept_3_3 17 49 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  49 151 (Polychromatic418967fa.accept_21_16_7_4_1_3448 16 49 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 49 151 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 49 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 49 151 (accept_3_3 14 49 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 49 151 (Polychromatic418967fa.accept_11_2_5_8_1_470 13 49 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 151
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 49 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 49 151 (accept_3_3 11 49 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  49 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 49 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 49 151 (Polychromatic418967fa.accept_23_9_3_13_1_6352 9 49 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 151 (accept_3_3 8 49 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 49 151 (Polychromatic418967fa.accept_13_7_10_8_1_567 7 49 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 49 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 49 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 49 151 (accept_3_3 5 49 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49
  151 (Polychromatic418967fa.accept_13_4_10_8_1_1817 4 49 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 49 151 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 49 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 151 (accept_3_3 2 49 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 49 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 151)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 48 151 (allA_succ_of_accept 47 48 151 (accept_3_3 47 48 151 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 48 151 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 48 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 48 151 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 48 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 48 151 (accept_3_3 44 48 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 151 (Polychromatic418967fa.accept_10_3_8_1_1_182
  43 48 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 48 151
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 48 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 48 151 (accept_3_3 41 48 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  48 151 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 48 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 48 151 (Polychromatic418967fa.accept_10_9_8_1_1_1331 39 48 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 48 151 (accept_3_3 38 48 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 151 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 48 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 151
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 36 48 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 48 151 (accept_3_3 35 48 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  48 151 (Polychromatic418967fa.accept_11_1_4_8_1_1918 34 48 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 48 151 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 48 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 48 151 (accept_3_3 32 48 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 151 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 48 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 151
  (Polychromatic418967fa.accept_7_2_6_4_1_29 30 48 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 48 151 (accept_3_3 29 48 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  48 151 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 48 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 48 151 (Polychromatic418967fa.accept_13_1_9_8_1_1734 27 48 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 48 151 (accept_3_3 26 48 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 151 (Polychromatic418967fa.accept_13_12_9_8_1_2595 25 48 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 151
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 48 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 48 151 (accept_3_3 23 48 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  48 151 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 48 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 48 151 (Polychromatic418967fa.accept_15_6_3_1_1_3678 21 48 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 48 151 (accept_3_3 20 48 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 151 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 48 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 48 151
  (Polychromatic418967fa.accept_11_7_4_8_1_1371 18 48 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 48 151 (accept_3_3 17 48 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  48 151 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 48 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 48 151 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 48 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 48 151 (accept_3_3 14 48 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 151 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 48 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 48 151
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 48 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 48 151 (accept_3_3 11 48 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  48 151 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 48 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 48 151 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 48 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 48 151 (accept_3_3 8 48 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 151 (Polychromatic418967fa.accept_11_7_4_8_1_1371 7 48 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 151
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 48 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 48 151 (accept_3_3 5 48 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48
  151 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 48 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 48 151 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 48 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 48 151 (accept_3_3 2 48 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 48 151 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 48 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48 151)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  47 151 (allA_of_3_1 47 47 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 46 151 (allA_succ_of_accept 45 46
  151 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 46 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 46 151 (accept_3_3 44 46 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  46 151 (Polychromatic418967fa.accept_14_1_4_11_1_3036 43 46 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 46 151 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 46 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 151 (accept_3_3 41 46 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 46 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 46 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 46 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 46 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 46 151 (accept_3_3 38 46 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  46 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 46 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 46 151 (Polychromatic418967fa.accept_13_10_7_8_1_1794 36 46 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 46 151 (accept_3_3 35 46 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 46 151 (Polychromatic418967fa.accept_20_14_6_11_1_6600 34 46
  151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 46 151
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 46 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 46 151 (accept_3_3 32 46 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  46 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 46 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 46 151 (Polychromatic418967fa.accept_9_3_1_7_1_97 30 46 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 46 151 (accept_3_3 29 46 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 46 151 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 46 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 46 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 46 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 46 151 (accept_3_3 26 46 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  46 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 46 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 46 151 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 46 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 151 (accept_3_3 23 46 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 46 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 46 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 46 151
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 46 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 46 151 (accept_3_3 20 46 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  46 151 (Polychromatic418967fa.accept_24_19_22_7_1_8111 19 46 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 46 151 (Polychromatic418967fa.accept_17_1_12_15_1_1263 18 46 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 151 (accept_3_3 17 46 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 46 151 (Polychromatic418967fa.accept_11_5_2_8_1_866 16 46 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 46 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 46 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 46 151 (accept_3_3 14 46 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  46 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 46 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 46 151 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 46 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 46 151 (accept_3_3 11 46 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 46 151 (Polychromatic418967fa.accept_13_10_7_8_1_1794 10 46 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 46 151
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 46 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 46 151 (accept_3_3 8 46 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 46
  151 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 46 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 46 151 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 46 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 46 151 (accept_3_3 5 46 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 46 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 46 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 46 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 46
  151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 46 151 (accept_3_3 2 46 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 46 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 46
  151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  151)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 151 (allA_succ_of_accept 44 45 151 (accept_3_3 44 45
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 151
  (Polychromatic418967fa.accept_7_1_3_4_1_128 43 45 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 45 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 45 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 151 (accept_3_3 41 45 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 45 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 45 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 151 (Polychromatic418967fa.accept_10_9_5_1_1_1325
  39 45 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 151 (accept_3_3 38
  45 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 151
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 37 45 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 45 151 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 45 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 45 151 (accept_3_3 35 45 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 45 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 45 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 151
  (Polychromatic418967fa.accept_17_16_11_15_1_4353 33 45 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 45 151 (accept_3_3 32 45 151 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 151 (Polychromatic418967fa.accept_19_12_7_18_1_8110 31 45 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 45 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 45 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 45 151 (accept_3_3 29 45 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 28
  45 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 151
  (Polychromatic418967fa.accept_7_6_3_4_1_294 27 45 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 45 151 (accept_3_3 26 45 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  45 151 (Polychromatic418967fa.accept_16_9_13_7_1_1509 25 45 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 45 151 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 45 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 45 151 (accept_3_3 23 45 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 45 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 151
  (Polychromatic418967fa.accept_14_7_3_11_1_2199 21 45 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 45 151 (accept_3_3 20 45 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  45 151 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 45 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 45 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 45 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 151 (accept_3_3 17 45 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 45 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 151
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 45 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 45 151 (accept_3_3 14 45 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  45 151 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 45 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 45 151 (Polychromatic418967fa.accept_19_12_7_18_1_8110 12 45 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 45 151 (accept_3_3 11 45 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 45 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 151
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 45 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 45 151 (accept_3_3 8 45 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45
  151 (Polychromatic418967fa.accept_14_7_3_11_1_2199 7 45 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 45 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 45 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 45 151 (accept_3_3 5 45 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 45 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 45 151
  (Polychromatic418967fa.accept_12_3_9_7_1_472 3 45 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 45 151 (accept_3_3 2 45 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45
  151 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 45 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 45 151))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 151 (allA_of_3_1 44 44 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 43 151 (allA_succ_of_accept 42 43 151
  (Polychromatic418967fa.accept_10_2_3_1_1_481 42 43 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 151 (accept_3_3 41 43 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 151 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 43 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 151 (Polychromatic418967fa.accept_19_1_5_18_1_8109 39 43 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 151 (accept_3_3 38 43 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 151 (Polychromatic418967fa.accept_13_11_4_8_1_1098 37 43
  151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 151
  (Polychromatic418967fa.accept_8_4_3_7_1_491 36 43 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 151 (accept_3_3 35 43 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 151 (Polychromatic418967fa.accept_16_2_11_7_1_2352 34 43 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 151 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 43 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 151 (accept_3_3 32 43 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 151 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 43 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 151
  (Polychromatic418967fa.accept_20_10_3_11_1_8108 30 43 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 151 (accept_3_3 29 43 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 151 (Polychromatic418967fa.accept_8_4_3_7_1_491 28 43 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 151 (Polychromatic418967fa.accept_15_12_13_1_1_3695 27 43 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 151 (accept_3_3 26 43 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 151 (Polychromatic418967fa.accept_13_12_4_8_1_1120 25 43
  151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 151
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 43 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 151 (accept_3_3 23 43 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 151 (Polychromatic418967fa.accept_10_2_3_1_1_481 22 43 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 151 (Polychromatic418967fa.accept_16_5_11_7_1_5635 21 43 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 151 (accept_3_3 20 43 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 151 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 43 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 151
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 43 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 151 (accept_3_3 17 43 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 151 (Polychromatic418967fa.accept_22_16_21_19_1_8107 16 43 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 151 (Polychromatic418967fa.accept_16_15_11_7_1_6951 15 43 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 151 (accept_3_3 14 43 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 151 (Polychromatic418967fa.accept_19_13_5_18_1_8106 13 43
  151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 151
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 43 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 151 (accept_3_3 11 43 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 151 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 43 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 151 (Polychromatic418967fa.accept_11_9_10_8_1_444 9 43 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 151 (accept_3_3 8 43 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 151 (Polychromatic418967fa.accept_17_7_9_15_1_8105 7 43 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 151
  (Polychromatic418967fa.accept_17_6_9_15_1_3185 6 43 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 151 (accept_3_3 5 43 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  151 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 43 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 151 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 43 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 151 (accept_3_3 2 43 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 151 (Polychromatic418967fa.accept_17_1_9_15_1_3186 1 43 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 151))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 151
  (allA_succ_of_accept 41 42 151 (accept_3_3 41 42 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  42 151 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 42 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 42 151 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 42 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 42 151 (accept_3_3 38 42 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 42 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 151
  (Polychromatic418967fa.accept_10_6_2_1_1_494 36 42 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 42 151 (accept_3_3 35 42 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  42 151 (Polychromatic418967fa.accept_15_4_12_1_1_1081 34 42 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 42 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 42 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 42 151 (accept_3_3 32 42 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 151 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 42 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 42 151
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 42 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 42 151 (accept_3_3 29 42 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  42 151 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 42 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 42 151 (Polychromatic418967fa.accept_17_10_8_15_1_8104 27 42 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 42 151 (accept_3_3 26 42 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 42 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 151
  (Polychromatic418967fa.accept_13_11_3_8_1_1786 24 42 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 42 151 (accept_3_3 23 42 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  42 151 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 42 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 42 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 42 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 42 151 (accept_3_3 20 42 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 151 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 42 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 42 151
  (Polychromatic418967fa.accept_13_5_3_8_1_1117 18 42 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 42 151 (accept_3_3 17 42 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  42 151 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 42 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 42 151 (Polychromatic418967fa.accept_19_15_4_18_1_5227 15 42 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 42 151 (accept_3_3 14 42 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 42 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 151
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 42 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 42 151 (accept_3_3 11 42 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  42 151 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 42 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 42 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 42 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 42 151 (accept_3_3 8 42 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 151 (Polychromatic418967fa.accept_13_7_3_8_1_1750 7 42 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 42 151
  (Polychromatic418967fa.accept_10_6_2_1_1_494 6 42 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 42 151 (accept_3_3 5 42 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42
  151 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 42 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 42 151 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 42 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 42 151 (accept_3_3 2 42 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 42 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 42 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42 151)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 151
  (allA_of_3_1 41 41 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 40 151 (allA_succ_of_accept 39 40 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 40 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 40 151 (accept_3_3 38 40 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  40 151 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 40 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 40 151 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 40 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 40 151 (accept_3_3 35 40 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 40 151 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 40 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 40 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 40 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 40 151 (accept_3_3 32 40 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  40 151 (Polychromatic418967fa.accept_13_5_1_8_1_1115 31 40 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 40 151 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 40 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 40 151 (accept_3_3 29 40 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 40 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 40 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 40 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 40 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 40 151 (accept_3_3 26 40 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  40 151 (Polychromatic418967fa.accept_13_12_1_8_1_1779 25 40 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 40 151 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 40 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 40 151 (accept_3_3 23 40 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 40 151 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 40 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 40 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 40 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 40 151 (accept_3_3 20 40 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  40 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 40 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 40 151 (Polychromatic418967fa.accept_13_5_1_8_1_1115 18 40 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 40 151 (accept_3_3 17 40 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 40 151 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 40 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 40 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 40 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 40 151 (accept_3_3 14 40 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  40 151 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 40 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 40 151 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 40 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 40 151 (accept_3_3 11 40 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 40 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 40 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 40 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 40 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 40 151 (accept_3_3 8 40 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 40
  151 (Polychromatic418967fa.accept_13_7_1_8_1_1778 7 40 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 40 151 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 40 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 40 151 (accept_3_3 5 40 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 40 151 (Polychromatic418967fa.accept_11_4_7_8_1_1926 4 40 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 40 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 40 151 (accept_3_3 2 40 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40
  151 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 40 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 40 151)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 151 (allA_succ_of_accept 38 39 151 (accept_3_3
  38 39 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 151
  (Polychromatic418967fa.accept_9_1_3_7_1_6 37 39 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 39 151 (Polychromatic418967fa.accept_11_3_6_8_1_1924 36 39 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 39 151 (accept_3_3 35 39 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 39 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 39 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 151 (Polychromatic418967fa.accept_9_6_3_7_1_580 33
  39 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 151 (accept_3_3 32 39
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 151
  (Polychromatic418967fa.accept_9_4_3_7_1_296 31 39 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 39 151 (Polychromatic418967fa.accept_17_13_5_15_1_8103 30 39 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 39 151 (accept_3_3 29 39 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 39 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 39 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 151
  (Polychromatic418967fa.accept_17_10_5_15_1_4332 27 39 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 39 151 (accept_3_3 26 39 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  39 151 (Polychromatic418967fa.accept_10_5_9_1_1_187 25 39 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 39 151 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 39 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 39 151 (accept_3_3 23 39 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 39 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 151
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 39 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 39 151 (accept_3_3 20 39 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  39 151 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 39 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 39 151 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 39 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 39 151 (accept_3_3 17 39 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 39 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 151
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 39 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 39 151 (accept_3_3 14 39 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  39 151 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 39 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 39 151 (Polychromatic418967fa.accept_10_2_9_1_1_185 12 39 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 39 151 (accept_3_3 11 39 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 39 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 151
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 39 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 39 151 (accept_3_3 8 39 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39
  151 (Polychromatic418967fa.accept_15_7_9_1_1_473 7 39 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 39 151 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 39 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 39 151 (accept_3_3 5 39 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 39 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 39 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 39 151 (Polychromatic418967fa.accept_11_3_6_8_1_1924 3
  39 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 151 (accept_3_3 2 39 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 151 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 39
  151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39
  151))))))))))))))))))))))))))))))))))))))) (allB_succ 38 151 (allA_of_3_1 38 38 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 37 151 (allA_succ_of_accept 36 37 151 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 37 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 151 (accept_3_3 35 37 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 37 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 34
  37 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 151
  (Polychromatic418967fa.accept_7_5_2_4_1_126 33 37 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 37 151 (accept_3_3 32 37 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  37 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 37 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 37 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 37 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 151 (accept_3_3 29 37 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 37 151 (Polychromatic418967fa.accept_16_12_5_7_1_2360 28 37 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 151
  (Polychromatic418967fa.accept_7_6_2_4_1_291 27 37 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 37 151 (accept_3_3 26 37 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  37 151 (Polychromatic418967fa.accept_15_10_7_1_1_3686 25 37 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 37 151 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 37 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 151 (accept_3_3 23 37 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 37 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 37 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 151
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 37 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 37 151 (accept_3_3 20 37 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  37 151 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 37 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 37 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 37 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 151 (accept_3_3 17 37 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 37 151 (Polychromatic418967fa.accept_10_6_7_1_1_1297 16 37 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 151
  (Polychromatic418967fa.accept_9_6_1_7_1_577 15 37 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 37 151 (accept_3_3 14 37 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  37 151 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 37 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 37 151 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 37 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 37 151 (accept_3_3 11 37 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 37 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 37 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 151
  (Polychromatic418967fa.accept_13_9_11_8_1_195 9 37 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 37 151 (accept_3_3 8 37 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37
  151 (Polychromatic418967fa.accept_11_7_4_8_1_1371 7 37 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 37 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 37 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 37 151 (accept_3_3 5 37 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 37 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 37 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 37 151
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 37 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 37 151 (accept_3_3 2 37 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 37
  151 (Polychromatic418967fa.accept_11_1_4_8_1_1918 1 37 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 37 151))))))))))))))))))))))))))))))))))))) (allB_succ 36 151 (allA_succ_of_accept 35 36 151
  (accept_3_3 35 36 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 36 151
  (Polychromatic418967fa.accept_25_9_11_1_1_8102 34 36 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 36 151 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 36 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 36 151 (accept_3_3 32 36 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 36 151 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 36 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 36 151 (Polychromatic418967fa.accept_13_4_10_8_1_1817
  30 36 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 36 151 (accept_3_3 29
  36 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 36 151
  (Polychromatic418967fa.accept_11_6_3_8_1_843 28 36 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 36 151 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 36 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 36 151 (accept_3_3 26 36 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 36 151 (Polychromatic418967fa.accept_10_5_6_1_1_836 25 36 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 36 151 (Polychromatic418967fa.accept_7_3_1_4_1_121 24
  36 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 36 151 (accept_3_3 23 36
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 36 151
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 36 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 36 151 (Polychromatic418967fa.accept_17_4_2_15_1_1254 21 36 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 36 151 (accept_3_3 20 36 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 36 151 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 36 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 151 (Polychromatic418967fa.accept_13_5_10_8_1_1127
  18 36 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 36 151 (accept_3_3 17
  36 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 36 151
  (Polychromatic418967fa.accept_11_5_3_8_1_454 16 36 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 36 151 (Polychromatic418967fa.accept_10_5_6_1_1_836 15 36 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 36 151 (accept_3_3 14 36 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 36 151 (Polychromatic418967fa.accept_16_13_4_7_1_1537 13 36 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 36 151
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 36 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 36 151 (accept_3_3 11 36 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  36 151 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 36 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 36 151 (Polychromatic418967fa.accept_15_9_6_1_1_493 9 36 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 36 151 (accept_3_3 8 36 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 151 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 36 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 36 151
  (Polychromatic418967fa.accept_11_6_3_8_1_843 6 36 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 36 151 (accept_3_3 5 36 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 36
  151 (Polychromatic418967fa.accept_13_4_10_8_1_1817 4 36 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 36 151 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 36 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 36 151 (accept_3_3 2 36 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 151 (Polychromatic418967fa.accept_19_1_17_18_1_8101 1 36 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 151)))))))))))))))))))))))))))))))))))) (allB_succ 35
  151 (allA_of_3_1 35 35 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 34 151 (allA_succ_of_accept 33 34 151
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 34 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 34 151 (accept_3_3 32 34 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  34 151 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 34 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 34 151 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 34 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 151 (accept_3_3 29 34 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 34 151 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 34 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 34 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 34 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 34 151 (accept_3_3 26 34 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  34 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 34 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 34 151 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 34 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 151 (accept_3_3 23 34 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 34 151 (Polychromatic418967fa.accept_18_4_16_7_1_1873 22 34 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 34 151
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 34 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 34 151 (accept_3_3 20 34 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  34 151 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 34 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 34 151 (Polychromatic418967fa.accept_15_3_4_1_1_1072 18 34 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 34 151 (accept_3_3 17 34 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 34 151 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 34 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 34 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 34 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 34 151 (accept_3_3 14 34 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  34 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 34 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 34 151 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 34 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 151 (accept_3_3 11 34 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 34 151 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 34 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 34 151
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 34 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 34 151 (accept_3_3 8 34 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 34
  151 (Polychromatic418967fa.accept_10_7_4_1_1_1319 7 34 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 34 151 (Polychromatic418967fa.accept_20_6_14_11_1_6537 6 34 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 151 (accept_3_3 5 34 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 34 151 (Polychromatic418967fa.accept_11_4_1_8_1_1366 4 34 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 34 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 34 151 (accept_3_3 2 34 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34
  151 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 34 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 34 151)))))))))))))))))))))))))))))))))) (allB_succ 33 151 (allA_succ_of_accept 32 33 151 (accept_3_3 32 33
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 151
  (Polychromatic418967fa.accept_9_4_6_7_1_286 31 33 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 33 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 33 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 151 (accept_3_3 29 33 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 33 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 33 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 151 (Polychromatic418967fa.accept_7_6_5_4_1_297 27
  33 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 151 (accept_3_3 26 33
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 151
  (Polychromatic418967fa.accept_13_12_7_8_1_1104 25 33 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 33 151 (Polychromatic418967fa.accept_16_8_1_7_1_2355 24 33 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 151 (accept_3_3 23 33 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 33 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 33 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 151 (Polychromatic418967fa.accept_9_3_6_7_1_562 21
  33 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 151 (accept_3_3 20 33
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 151
  (Polychromatic418967fa.accept_9_1_6_7_1_285 19 33 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 33 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 33 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 151 (accept_3_3 17 33 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 33 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 33 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 151 (Polychromatic418967fa.accept_7_1_5_4_1_134 15
  33 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 151 (accept_3_3 14 33
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 151
  (Polychromatic418967fa.accept_7_6_5_4_1_297 13 33 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 33 151 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 33 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 151 (accept_3_3 11 33 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 33 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 33 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 151 (Polychromatic418967fa.accept_7_2_5_4_1_115 9
  33 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 151 (accept_3_3 8 33 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 151 (Polychromatic418967fa.accept_19_7_14_18_1_6654
  7 33 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 151
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 33 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 151 (accept_3_3 5 33 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33
  151 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 33 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 33 151 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 33 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 151 (accept_3_3 2 33 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 33 151 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 33 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 151))))))))))))))))))))))))))))))))) (allB_succ 32 151
  (allA_of_3_1 32 32 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 31 151 (allA_succ_of_accept 30 31 151
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 31 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 31 151 (accept_3_3 29 31 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  31 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 31 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 31 151 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 31 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 151 (accept_3_3 26 31 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 151 (Polychromatic418967fa.accept_13_12_5_8_1_1101 25 31 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 151
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 31 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 151 (accept_3_3 23 31 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  31 151 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 31 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 31 151 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 31 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 151 (accept_3_3 20 31 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 31 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 151
  (Polychromatic418967fa.accept_22_18_9_19_1_8100 18 31 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 151 (accept_3_3 17 31 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 151 (Polychromatic418967fa.accept_13_3_5_8_1_1099 16 31 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 151 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 31 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 151 (accept_3_3 14 31 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 151 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 31 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 151
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 31 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 151 (accept_3_3 11 31 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 151 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 31 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 151 (Polychromatic418967fa.accept_19_9_12_18_1_8099 9 31 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 151 (accept_3_3 8 31 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 151 (Polychromatic418967fa.accept_14_7_3_11_1_2199 7 31 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 151
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 31 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 151 (accept_3_3 5 31 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  151 (Polychromatic418967fa.accept_18_4_13_7_1_5395 4 31 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 31 151 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 31 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 151 (accept_3_3 2 31 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 151 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 31 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 151))))))))))))))))))))))))))))))) (allB_succ 30 151
  (allA_succ_of_accept 29 30 151 (accept_3_3 29 30 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  30 151 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 30 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 30 151 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 30 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 30 151 (accept_3_3 26 30 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 30 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 30 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 30 151
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 30 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 30 151 (accept_3_3 23 30 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  30 151 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 30 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 30 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 30 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 30 151 (accept_3_3 20 30 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 151 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 30 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 151
  (Polychromatic418967fa.accept_21_18_9_4_1_4964 18 30 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 30 151 (accept_3_3 17 30 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  30 151 (Polychromatic418967fa.accept_21_16_9_4_1_8098 16 30 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 30 151 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 30 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 30 151 (accept_3_3 14 30 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 30 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 151
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 30 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 30 151 (accept_3_3 11 30 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  30 151 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 30 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 30 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 30 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 30 151 (accept_3_3 8 30 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 151 (Polychromatic418967fa.accept_19_7_11_18_1_6680 7 30 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 30 151
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 30 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 30 151 (accept_3_3 5 30 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 30
  151 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 30 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 30 151 (Polychromatic418967fa.accept_18_3_12_7_1_6728 3 30 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 30 151 (accept_3_3 2 30 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 30 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 30 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 151)))))))))))))))))))))))))))))) (allB_succ 29 151 (allA_of_3_1
  29 29 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 28 151 (allA_succ_of_accept 27 28 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 28 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 28 151 (accept_3_3 26 28 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  28 151 (Polychromatic418967fa.accept_11_3_6_8_1_1924 25 28 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 28 151 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 28 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 151 (accept_3_3 23 28 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 28 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 28 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 28 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 28 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 28 151 (accept_3_3 20 28 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  28 151 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 28 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 28 151 (Polychromatic418967fa.accept_15_3_13_1_1_479 18 28 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 28 151 (accept_3_3 17 28 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 28 151 (Polychromatic418967fa.accept_17_16_11_15_1_4353 16 28 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 28 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 28 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 28 151 (accept_3_3 14 28 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  28 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 28 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 28 151 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 28 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 28 151 (accept_3_3 11 28 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 28 151 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 28 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 28 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 28 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 28 151 (accept_3_3 8 28 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 28
  151 (Polychromatic418967fa.accept_13_7_2_8_1_1746 7 28 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 28 151 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 28 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 28 151 (accept_3_3 5 28 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 28 151 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 28 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 28 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 28 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 28 151 (accept_3_3 2 28 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 28
  151 (Polychromatic418967fa.accept_20_1_8_11_1_8097 1 28 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 28 151)))))))))))))))))))))))))))) (allB_succ 27 151 (allA_succ_of_accept 26 27 151 (accept_3_3
  26 27 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 151
  (Polychromatic418967fa.accept_11_3_5_8_1_458 25 27 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 27 151 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 27 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 151 (accept_3_3 23 27 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 27 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 27 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 151 (Polychromatic418967fa.accept_12_9_3_7_1_924
  21 27 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 151 (accept_3_3 20
  27 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 151
  (Polychromatic418967fa.accept_7_5_6_4_1_117 19 27 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 27 151 (Polychromatic418967fa.accept_13_5_1_8_1_1115 18 27 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 151 (accept_3_3 17 27 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 27 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 27 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 151
  (Polychromatic418967fa.accept_16_15_11_7_1_6951 15 27 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 27 151 (accept_3_3 14 27 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  27 151 (Polychromatic418967fa.accept_11_2_5_8_1_470 13 27 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 27 151 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 27 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 151 (accept_3_3 11 27 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 27 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 151
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 27 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 27 151 (accept_3_3 8 27 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27
  151 (Polychromatic418967fa.accept_13_7_1_8_1_1778 7 27 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 27 151 (Polychromatic418967fa.accept_10_6_7_1_1_1297 6 27 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 151 (accept_3_3 5 27 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 27 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 151
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 27 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 27 151 (accept_3_3 2 27 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27
  151 (Polychromatic418967fa.accept_19_1_8_18_1_6667 1 27 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 27 151))))))))))))))))))))))))))) (allB_succ 26 151 (allA_of_3_1 26 26 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 25 151 (allA_succ_of_accept 24 25 151 (Polychromatic418967fa.accept_10_4_5_1_1_497 24
  25 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 151 (accept_3_3 23 25
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 25 151 (Polychromatic418967fa.accept_4_2_1_3_1_27
  22 25 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 151
  (Polychromatic418967fa.accept_15_6_10_1_1_3675 21 25 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 25 151 (accept_3_3 20 25 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  25 151 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 25 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 25 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 25 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 151 (accept_3_3 17 25 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 25 151 (Polychromatic418967fa.accept_10_6_5_1_1_482 16 25 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 25 151
  (Polychromatic418967fa.accept_20_15_5_11_1_8096 15 25 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 25 151 (accept_3_3 14 25 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  25 151 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 25 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 25 151 (Polychromatic418967fa.accept_19_12_6_18_1_8095 12 25 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 151 (accept_3_3 11 25 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 25 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 25 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 25 151
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 25 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 25 151 (accept_3_3 8 25 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25
  151 (Polychromatic418967fa.accept_13_7_12_8_1_199 7 25 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 25 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 25 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 25 151 (accept_3_3 5 25 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 25 151 (Polychromatic418967fa.accept_10_4_5_1_1_497 4 25 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 151
  (Polychromatic418967fa.accept_16_3_9_7_1_6842 3 25 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 25 151 (accept_3_3 2 25 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25
  151 (Polychromatic418967fa.accept_13_1_12_8_1_1818 1 25 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 25 151))))))))))))))))))))))))) (allB_succ 24 151 (allA_succ_of_accept 23 24 151 (accept_3_3 23
  24 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 151
  (Polychromatic418967fa.accept_7_1_3_4_1_128 22 24 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 24 151 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 24 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 24 151 (accept_3_3 20 24 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 24 151 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 24 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 24 151 (Polychromatic418967fa.accept_21_18_3_4_1_5013
  18 24 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 24 151 (accept_3_3 17
  24 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 151
  (Polychromatic418967fa.accept_11_5_2_8_1_866 16 24 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 24 151 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 24 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 24 151 (accept_3_3 14 24 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 24 151 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 24 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 24 151 (Polychromatic418967fa.accept_9_3_6_7_1_562 12
  24 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 24 151 (accept_3_3 11 24
  151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 24 151
  (Polychromatic418967fa.accept_9_1_6_7_1_285 10 24 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 24 151 (Polychromatic418967fa.accept_13_9_11_8_1_195 9 24 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 24 151 (accept_3_3 8 24 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 24 151 (Polychromatic418967fa.accept_10_7_4_1_1_1319 7 24 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 24 151 (Polychromatic418967fa.accept_7_6_3_4_1_294 6
  24 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 24 151 (accept_3_3 5 24 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24 151 (Polychromatic418967fa.accept_9_4_6_7_1_286 4
  24 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 24 151
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 24 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 24 151 (accept_3_3 2 24 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 24
  151 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 24 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 24 151)))))))))))))))))))))))) (allB_succ 23 151 (allA_of_3_1 23 23 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 22 151 (allA_succ_of_accept 21 22 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 22 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 22 151 (accept_3_3 20 22 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 22 151 (Polychromatic418967fa.accept_7_5_1_4_1_122 19
  22 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 22 151
  (Polychromatic418967fa.accept_14_4_8_11_1_794 18 22 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 22 151 (accept_3_3 17 22 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  22 151 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 22 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 22 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 22 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 22 151 (accept_3_3 14 22 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 22 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 22 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 22 151
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 22 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 22 151 (accept_3_3 11 22 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  22 151 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 22 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 22 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 22 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 22 151 (accept_3_3 8 22 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 22 151 (Polychromatic418967fa.accept_13_7_9_8_1_188 7 22 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 22 151
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 22 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 22 151 (accept_3_3 5 22 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 22
  151 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 22 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 22 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 22 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 22 151 (accept_3_3 2 22 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 22 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 22 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 151)))))))))))))))))))))) (allB_succ 21 151
  (allA_succ_of_accept 20 21 151 (accept_3_3 20 21 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  21 151 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 21 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 21 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 21 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 151 (accept_3_3 17 21 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 21 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 151
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 21 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 21 151 (accept_3_3 14 21 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  21 151 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 21 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 21 151 (Polychromatic418967fa.accept_16_12_5_7_1_2360 12 21 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 151 (accept_3_3 11 21 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 21 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 151
  (Polychromatic418967fa.accept_11_9_10_8_1_444 9 21 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 21 151 (accept_3_3 8 21 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21
  151 (Polychromatic418967fa.accept_15_7_6_1_1_1091 7 21 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 21 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 21 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 151 (accept_3_3 5 21 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 21 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21 151
  (Polychromatic418967fa.accept_12_3_9_7_1_472 3 21 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 21 151 (accept_3_3 2 21 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21
  151 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 21 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 21 151))))))))))))))))))))) (allB_succ 20 151 (allA_of_3_1 20 20 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 19 151 (allA_succ_of_accept 18 19 151 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 19 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 19 151 (accept_3_3 17 19 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 19 151 (Polychromatic418967fa.accept_7_2_5_4_1_115 16
  19 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 19 151
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 19 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 19 151 (accept_3_3 14 19 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  19 151 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 19 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 19 151 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 19 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 19 151 (accept_3_3 11 19 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 19 151 (Polychromatic418967fa.accept_16_10_3_7_1_8094 10 19 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 19 151
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 19 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 19 151 (accept_3_3 8 19 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 19
  151 (Polychromatic418967fa.accept_17_7_2_15_1_1255 7 19 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 19 151 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 19 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 19 151 (accept_3_3 5 19 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 19 151 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 19 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 19 151
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 19 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 19 151 (accept_3_3 2 19 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 19
  151 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 19 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 19 151))))))))))))))))))) (allB_succ 18 151 (allA_succ_of_accept 17 18 151 (accept_3_3 17 18 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 151 (Polychromatic418967fa.accept_13_3_5_8_1_1099 16 18 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 18 151
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 15 18 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 18 151 (accept_3_3 14 18 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  18 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 18 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 18 151 (Polychromatic418967fa.accept_13_12_5_8_1_1101 12 18 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 18 151 (accept_3_3 11 18 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 151 (Polychromatic418967fa.accept_13_10_5_8_1_2555 10 18
  151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 18 151
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 18 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 18 151 (accept_3_3 8 18 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 18
  151 (Polychromatic418967fa.accept_14_7_4_11_1_3038 7 18 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 18 151 (Polychromatic418967fa.accept_15_6_3_1_1_3678 6 18 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 18 151 (accept_3_3 5 18 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 151 (Polychromatic418967fa.accept_11_4_7_8_1_1926 4 18 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 18 151
  (Polychromatic418967fa.accept_10_3_8_1_1_182 3 18 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 18 151 (accept_3_3 2 18 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18
  151 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 18 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 18 151)))))))))))))))))) (allB_succ 17 151 (allA_of_3_1 17 17 151 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 16 151 (allA_succ_of_accept 15 16 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 16 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 16 151 (accept_3_3 14 16 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 16 151 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 16 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 16 151
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 16 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 16 151 (accept_3_3 11 16 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  16 151 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 16 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 16 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 16 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 16 151 (accept_3_3 8 16 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 16 151 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 16 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 16 151
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 16 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 16 151 (accept_3_3 5 16 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 16
  151 (Polychromatic418967fa.accept_17_4_16_15_1_1212 4 16 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 16 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 16 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 16 151 (accept_3_3 2 16 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 16 151 (Polychromatic418967fa.accept_17_1_16_15_1_4315 1 16 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 151)))))))))))))))) (allB_succ 15 151
  (allA_succ_of_accept 14 15 151 (accept_3_3 14 15 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  15 151 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 15 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 15 151 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 15 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 151 (accept_3_3 11 15 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 15 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 151
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 15 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 15 151 (accept_3_3 8 15 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15
  151 (Polychromatic418967fa.accept_11_7_4_8_1_1371 7 15 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 15 151 (Polychromatic418967fa.accept_10_6_5_1_1_482 6 15 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 15 151 (accept_3_3 5 15 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 15 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 15 151
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 15 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 15 151 (accept_3_3 2 15 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15
  151 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 15 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 15 151))))))))))))))) (allB_succ 14 151 (allA_of_3_1 14 14 151 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 13 151 (allA_succ_of_accept 12 13 151 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 13 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 13 151 (accept_3_3 11 13 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 13 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 13 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 13 151
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 13 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 13 151 (accept_3_3 8 13 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 13
  151 (Polychromatic418967fa.accept_21_7_13_4_1_2169 7 13 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 13 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 13 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 13 151 (accept_3_3 5 13 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 13 151 (Polychromatic418967fa.accept_16_4_13_7_1_4522 4 13 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 13 151
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 13 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 13 151 (accept_3_3 2 13 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 13
  151 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 13 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 13 151))))))))))))) (allB_succ 12 151 (allA_succ_of_accept 11 12 151 (accept_3_3 11 12 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 151 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 12 151
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 12 151
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 12 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 12 151 (accept_3_3 8 12 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 12
  151 (Polychromatic418967fa.accept_13_7_12_8_1_199 7 12 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 12 151 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 12 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 12 151 (accept_3_3 5 12 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 151 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 12 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 12 151
  (Polychromatic418967fa.accept_8_3_4_7_1_475 3 12 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 12 151 (accept_3_3 2 12 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12
  151 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 12 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 12 151)))))))))))) (allB_succ 11 151 (allA_of_3_1 11 11 151 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 10 151 (allA_succ_of_accept 9 10 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 10 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 10 151 (accept_3_3 8 10 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 10 151 (Polychromatic418967fa.accept_13_7_10_8_1_567 7 10 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 10 151
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 10 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 10 151 (accept_3_3 5 10 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 10
  151 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 10 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 10 151 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 10 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 10 151 (accept_3_3 2 10 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 10 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 10 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 151)))))))))) (allB_succ 9 151 (allA_succ_of_accept 8 9 151
  (accept_3_3 8 9 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 151
  (Polychromatic418967fa.accept_13_7_9_8_1_188 7 9 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 9 151 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 9 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 151 (accept_3_3 5 9 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 9 151 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 9 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 151 (Polychromatic418967fa.accept_12_3_9_7_1_472 3 9
  151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 151 (accept_3_3 2 9 151
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 151 (Polychromatic418967fa.accept_13_1_9_8_1_1734 1
  9 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 151))))))))) (allB_succ 8 151
  (allA_of_3_1 8 8 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 7 151 (allA_succ_of_accept 6 7 151
  (Polychromatic418967fa.accept_10_6_7_1_1_1297 6 7 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 151 (accept_3_3 5 7 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 151
  (Polychromatic418967fa.accept_10_4_7_1_1_471 4 7 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 151 (Polychromatic418967fa.accept_13_3_7_8_1_4192 3 7 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 151 (accept_3_3 2 7 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 151 (Polychromatic418967fa.accept_13_1_7_8_1_1796 1 7 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 151))))))) (allB_succ 6 151 (allA_succ_of_accept 5 6 151
  (accept_3_3 5 6 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 6 151
  (Polychromatic418967fa.accept_9_4_6_7_1_286 4 6 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 6 151 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 6 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 6 151 (accept_3_3 2 6 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 6 151 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 6 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 151)))))) (allB_succ 5 151 (allA_of_3_1 5 5 151 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 4 151 (allA_succ_of_accept 3 4 151
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 4 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 151 (accept_3_3 2 4 151 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 151
  (Polychromatic418967fa.accept_9_1_4_7_1_7 1 4 151 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 151)))) (allB_succ 3 151 (allA_succ_of_accept 2 3 151 (accept_3_3 2 3 151 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 151 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 3 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 151))) (allB_succ 2 151 (allA_of_3_1 2 2 151 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  151)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


