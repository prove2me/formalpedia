-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch163
-- name    : Polychromatic418967fa_Branch163
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:17:41.243684+00:00
-- url     : https://prove2.me/theorems/62389282-ba4f-4149-a20c-26aa9712f0e8
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

def Polychromatic418967fa.branch_163 : allB 163 163 :=
  allB_succ' 2 162 163 (Eq.refl Bool.true) (allA_succ_of_accept 1 162 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 1
  162 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162 163)) (allB_succ' 3 161 163
  (Eq.refl Bool.true) (allA_of_3_1 3 161 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 160 163 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 160 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 160 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 160 163 (accept_3_3 2 160 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 160 163 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 160 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 160 163)))) (allB_succ' 5 159 163 (Eq.refl Bool.true)
  (allA_succ_of_accept 4 159 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 159 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 159 163 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 159 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 159 163 (accept_3_3 2 159 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 163 (Polychromatic418967fa.accept_13_1_3_7_1_1710
  1 159 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 159 163))))) (allB_succ' 6 158 163
  (Eq.refl Bool.true) (allA_of_3_1 6 158 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 157 163 (Eq.refl
  Bool.true) (allA_succ_of_accept 6 157 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 157 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 157 163 (accept_3_3 5 157 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 157 163 (Polychromatic418967fa.accept_10_4_7_3_1_54 4 157 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 157 163
  (Polychromatic418967fa.accept_9_3_4_1_1_22 3 157 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 157 163 (accept_3_3 2 157 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  157 163 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 157 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 157 163))))))) (allB_succ' 8 156 163 (Eq.refl Bool.true) (allA_succ_of_accept 7 156 163
  (Polychromatic418967fa.accept_8_7_4_3_1_156 7 156 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 156 163 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 156 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 156 163 (accept_3_3 5 156 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 156 163 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 156 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 156 163 (Polychromatic418967fa.accept_18_3_12_1_1_3787
  3 156 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 156 163 (accept_3_3 2
  156 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 156 163
  (Polychromatic418967fa.accept_22_1_2_9_1_9086 1 156 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 156 163)))))))) (allB_succ' 9 155 163 (Eq.refl Bool.true) (allA_of_3_1 9 155 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 10 154 163 (Eq.refl Bool.true) (allA_succ_of_accept 9 154 163
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 154 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 154 163 (accept_3_3 8 154 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  154 163 (Polychromatic418967fa.accept_10_7_4_3_1_560 7 154 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 154 163 (Polychromatic418967fa.accept_15_6_4_13_1_403 6 154 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 154 163 (accept_3_3 5 154 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 154 163 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 154 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 154 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 154 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 154 163 (accept_3_3 2 154 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  154 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 154 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 154 163)))))))))) (allB_succ' 11 153 163 (Eq.refl Bool.true) (allA_succ_of_accept 10 153 163
  (Polychromatic418967fa.accept_4_2_1_3_1_27 10 153 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 153 163 (Polychromatic418967fa.accept_15_9_3_13_1_1686 9 153 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 153 163 (accept_3_3 8 153 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 153 163 (Polychromatic418967fa.accept_16_7_9_3_1_1324 7 153 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 153 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 6
  153 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 153 163 (accept_3_3 5 153
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 163 (Polychromatic418967fa.accept_6_4_3_1_1_57
  4 153 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 153 163
  (Polychromatic418967fa.accept_7_3_6_2_1_90 3 153 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 153 163 (accept_3_3 2 153 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  153 163 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 153 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 153 163))))))))))) (allB_succ' 12 152 163 (Eq.refl Bool.true) (allA_of_3_1 12 152 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 151 163 (Eq.refl Bool.true) (allA_succ_of_accept 12 151 163
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 151 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 151 163 (accept_3_3 11 151 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 151 163 (Polychromatic418967fa.accept_11_10_8_9_1_492 10 151 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 151 163 (Polychromatic418967fa.accept_13_9_8_7_1_1073 9 151 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 151 163 (accept_3_3 8 151 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 151 163 (Polychromatic418967fa.accept_19_7_18_11_1_464 7 151 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 151 163
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 151 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 151 163 (accept_3_3 5 151 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  151 163 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 151 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 151 163 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 151 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 151 163 (accept_3_3 2 151 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 151 163 (Polychromatic418967fa.accept_13_1_8_7_1_1088 1 151 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 151 163))))))))))))) (allB_succ' 14 150 163 (Eq.refl
  Bool.true) (allA_succ_of_accept 13 150 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 150 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 150 163 (Polychromatic418967fa.accept_7_5_3_2_1_249
  12 150 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 150 163 (accept_3_3 11
  150 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 150 163
  (Polychromatic418967fa.accept_21_10_3_16_1_5909 10 150 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 150 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 150 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 150 163 (accept_3_3 8 150 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 150 163 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 150 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 150 163
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 150 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 150 163 (accept_3_3 5 150 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  150 163 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 150 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 150 163 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 150 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 150 163 (accept_3_3 2 150 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 150 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 150 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150 163)))))))))))))) (allB_succ' 15 149 163 (Eq.refl
  Bool.true) (allA_of_3_1 15 149 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 148 163 (Eq.refl Bool.true)
  (allA_succ_of_accept 15 148 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 148 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 148 163 (accept_3_3 14 148 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 148 163 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 148 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 148 163 (Polychromatic418967fa.accept_9_3_4_1_1_22 12
  148 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 148 163 (accept_3_3 11
  148 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 148 163
  (Polychromatic418967fa.accept_7_3_1_2_1_247 10 148 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 148 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 148 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 148 163 (accept_3_3 8 148 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 148 163 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 148 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 148 163 (Polychromatic418967fa.accept_7_6_1_2_1_230 6
  148 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 148 163 (accept_3_3 5 148
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 148 163
  (Polychromatic418967fa.accept_19_4_15_11_1_7498 4 148 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 148 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 148 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 148 163 (accept_3_3 2 148 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 148 163 (Polychromatic418967fa.accept_10_1_8_3_1_947 1 148 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 148 163)))))))))))))))) (allB_succ' 17 147 163 (Eq.refl Bool.true)
  (allA_succ_of_accept 16 147 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 147 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 147 163 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 147 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 147 163 (accept_3_3 14 147 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 147 163 (Polychromatic418967fa.accept_9_4_3_1_1_154
  13 147 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 147 163
  (Polychromatic418967fa.accept_13_12_4_7_1_2520 12 147 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 147 163 (accept_3_3 11 147 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 147 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 147 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 147 163 (Polychromatic418967fa.accept_12_9_3_7_1_924 9 147 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 147 163 (accept_3_3 8 147 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 163 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 147 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 147 163
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 147 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 147 163 (accept_3_3 5 147 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  147 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 147 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 147 163 (Polychromatic418967fa.accept_13_3_4_7_1_1711 3 147 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 147 163 (accept_3_3 2 147 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 163 (Polychromatic418967fa.accept_15_1_12_13_1_944 1 147 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 147 163))))))))))))))))) (allB_succ' 18 146 163 (Eq.refl
  Bool.true) (allA_of_3_1 18 146 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 145 163 (Eq.refl Bool.true)
  (allA_succ_of_accept 18 145 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 145 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 145 163 (accept_3_3 17 145 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 145 163 (Polychromatic418967fa.accept_15_1_10_13_1_939 16 145 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 145 163
  (Polychromatic418967fa.accept_11_4_2_9_1_496 15 145 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 145 163 (accept_3_3 14 145 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 145 163 (Polychromatic418967fa.accept_16_13_1_3_1_2205 13 145 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 145 163 (Polychromatic418967fa.accept_10_2_5_3_1_1408 12 145 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 145 163 (accept_3_3 11 145 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 145 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 145 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 145 163
  (Polychromatic418967fa.accept_13_9_2_7_1_1083 9 145 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 145 163 (accept_3_3 8 145 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  145 163 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 145 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 145 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 145 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 145 163 (accept_3_3 5 145 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 145 163 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 145 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 145 163
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 145 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 145 163 (accept_3_3 2 145 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  145 163 (Polychromatic418967fa.accept_15_1_10_13_1_939 1 145 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 145 163))))))))))))))))))) (allB_succ' 20 144 163 (Eq.refl Bool.true) (allA_succ_of_accept 19
  144 163 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 144 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 144 163 (Polychromatic418967fa.accept_15_3_9_13_1_1681 18 144 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 144 163 (accept_3_3 17 144 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 144 163 (Polychromatic418967fa.accept_13_3_1_7_1_1706 16 144
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 144 163
  (Polychromatic418967fa.accept_17_15_8_10_1_2886 15 144 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 144 163 (accept_3_3 14 144 163 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 144 163 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 144 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 144 163 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 144 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 144 163 (accept_3_3 11 144 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 144 163
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 10 144 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 144 163 (Polychromatic418967fa.accept_10_9_4_3_1_539 9 144 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 144 163 (accept_3_3 8 144 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 144 163 (Polychromatic418967fa.accept_10_7_4_3_1_560 7 144 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 144 163 (Polychromatic418967fa.accept_7_6_4_2_1_236 6
  144 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 144 163 (accept_3_3 5 144
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 144 163
  (Polychromatic418967fa.accept_15_4_9_13_1_2582 4 144 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 144 163 (Polychromatic418967fa.accept_13_3_1_7_1_1706 3 144 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 144 163 (accept_3_3 2 144 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 144 163 (Polychromatic418967fa.accept_20_1_4_3_1_9085 1 144 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144 163)))))))))))))))))))) (allB_succ' 21 143 163 (Eq.refl
  Bool.true) (allA_of_3_1 21 143 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 142 163 (Eq.refl Bool.true)
  (allA_succ_of_accept 21 142 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 142 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 142 163 (accept_3_3 20 142 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 142 163 (Polychromatic418967fa.accept_11_8_10_9_1_1401 19 142 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 142 163
  (Polychromatic418967fa.accept_13_5_12_7_1_1080 18 142 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 142 163 (accept_3_3 17 142 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 142 163 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 142 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 142 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 142 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 142 163 (accept_3_3 14 142 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 142 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 142 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 142 163
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 142 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 142 163 (accept_3_3 11 142 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 142 163 (Polychromatic418967fa.accept_13_10_12_7_1_1079 10 142 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 142 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 142 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 142 163 (accept_3_3 8 142 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 142 163 (Polychromatic418967fa.accept_14_7_2_9_1_2093 7 142 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 142 163
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 142 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 142 163 (accept_3_3 5 142 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  142 163 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 142 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 142 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 142 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 142 163 (accept_3_3 2 142 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 142 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 142 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142 163)))))))))))))))))))))) (allB_succ' 23 141 163
  (Eq.refl Bool.true) (allA_succ_of_accept 22 141 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 141 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 141 163
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 141 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 141 163 (accept_3_3 20 141 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 141 163 (Polychromatic418967fa.accept_15_4_6_13_1_956 19 141 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 141 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 141 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 141 163 (accept_3_3 17 141 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 141 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 141 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 141 163
  (Polychromatic418967fa.accept_12_3_9_7_1_472 15 141 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 141 163 (accept_3_3 14 141 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 141 163 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 141 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 141 163 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 141 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 141 163 (accept_3_3 11 141 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 141 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 141 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 141 163
  (Polychromatic418967fa.accept_13_9_11_7_1_1077 9 141 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 141 163 (accept_3_3 8 141 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  141 163 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 141 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 141 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 141 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 141 163 (accept_3_3 5 141 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 141 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 141 163
  (Polychromatic418967fa.accept_7_3_1_2_1_247 3 141 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 141 163 (accept_3_3 2 141 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  141 163 (Polychromatic418967fa.accept_13_1_11_7_1_1704 1 141 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 141 163))))))))))))))))))))))) (allB_succ' 24 140 163 (Eq.refl Bool.true) (allA_of_3_1 24 140
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 139 163 (Eq.refl Bool.true) (allA_succ_of_accept 24 139
  163 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 139 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 139 163 (accept_3_3 23 139 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 139 163 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 139 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 139 163 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 139 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 139 163 (accept_3_3 20 139 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 139 163 (Polychromatic418967fa.accept_13_6_9_7_1_2430 19 139 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 139 163
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 139 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 139 163 (accept_3_3 17 139 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 139 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 139 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 139 163 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 139 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 139 163 (accept_3_3 14 139 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 139 163 (Polychromatic418967fa.accept_11_2_7_9_1_890 13 139 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 139 163
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 139 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 139 163 (accept_3_3 11 139 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 139 163 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 139 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 139 163 (Polychromatic418967fa.accept_15_9_4_13_1_4482 9 139 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 139 163 (accept_3_3 8 139 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 139 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 139 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 139 163
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 139 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 139 163 (accept_3_3 5 139 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  139 163 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 139 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 139 163 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 139 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 139 163 (accept_3_3 2 139 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 139 163 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 139 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 139 163))))))))))))))))))))))))) (allB_succ' 26 138 163
  (Eq.refl Bool.true) (allA_succ_of_accept 25 138 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 138 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 138 163
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 138 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 138 163 (accept_3_3 23 138 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 138 163 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 138 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 138 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 138 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 138 163 (accept_3_3 20 138 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 138 163 (Polychromatic418967fa.accept_22_19_6_9_1_9026 19 138 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 138 163
  (Polychromatic418967fa.accept_7_4_5_2_1_243 18 138 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 138 163 (accept_3_3 17 138 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 138 163 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 138 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 138 163 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 138 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 138 163 (accept_3_3 14 138 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 138 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 138 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 138 163
  (Polychromatic418967fa.accept_13_12_8_7_1_2526 12 138 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 138 163 (accept_3_3 11 138 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 138 163 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 138 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 138 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 138 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 138 163 (accept_3_3 8 138 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 138 163 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 138 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 138 163
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 138 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 138 163 (accept_3_3 5 138 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  138 163 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 138 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 138 163 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 138 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 138 163 (accept_3_3 2 138 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 138 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 138 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138 163)))))))))))))))))))))))))) (allB_succ' 27 137 163
  (Eq.refl Bool.true) (allA_of_3_1 27 137 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 136 163 (Eq.refl
  Bool.true) (allA_succ_of_accept 27 136 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 136 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 136 163 (accept_3_3 26 136 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 136 163 (Polychromatic418967fa.accept_13_12_6_7_1_1071 25 136 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 136 163
  (Polychromatic418967fa.accept_11_2_4_9_1_484 24 136 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 136 163 (accept_3_3 23 136 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 136 163 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 136 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 136 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 136 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 136 163 (accept_3_3 20 136 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 136 163 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 136 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 136 163
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 136 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 136 163 (accept_3_3 17 136 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 136 163 (Polychromatic418967fa.accept_18_16_10_1_1_3696 16 136 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 136 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 136 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 136 163 (accept_3_3 14 136 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 136 163 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 136 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 136 163
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 136 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 136 163 (accept_3_3 11 136 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 136 163 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 136 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 136 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 136 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 136 163 (accept_3_3 8 136 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 136 163 (Polychromatic418967fa.accept_10_7_6_3_1_927 7 136 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 136 163
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 136 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 136 163 (accept_3_3 5 136 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  136 163 (Polychromatic418967fa.accept_13_4_6_7_1_2471 4 136 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 136 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 136 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 136 163 (accept_3_3 2 136 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 136 163 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 136 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 136 163)))))))))))))))))))))))))))) (allB_succ' 29 135
  163 (Eq.refl Bool.true) (allA_succ_of_accept 28 135 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 135 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 135 163
  (Polychromatic418967fa.accept_10_7_5_3_1_542 27 135 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 135 163 (accept_3_3 26 135 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 135 163 (Polychromatic418967fa.accept_13_12_5_7_1_1696 25 135 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 135 163 (Polychromatic418967fa.accept_13_11_5_7_1_2420 24 135 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 135 163 (accept_3_3 23 135 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 135 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 135 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 135 163
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 135 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 135 163 (accept_3_3 20 135 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 135 163 (Polychromatic418967fa.accept_25_19_10_13_1_9084 19 135 163 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 135 163 (Polychromatic418967fa.accept_10_8_5_3_1_543 18 135 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 135 163 (accept_3_3 17 135 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 135 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 135 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 135 163
  (Polychromatic418967fa.accept_13_2_5_7_1_1695 15 135 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 135 163 (accept_3_3 14 135 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 135 163 (Polychromatic418967fa.accept_19_13_2_11_1_9083 13 135 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 135 163 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 135 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 135 163 (accept_3_3 11 135 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 135 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 135 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 135 163
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 135 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 135 163 (accept_3_3 8 135 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  135 163 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 135 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 135 163 (Polychromatic418967fa.accept_11_6_3_9_1_906 6 135 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 135 163 (accept_3_3 5 135 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 135 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 135 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 135 163
  (Polychromatic418967fa.accept_18_3_9_1_1_3690 3 135 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 135 163 (accept_3_3 2 135 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  135 163 (Polychromatic418967fa.accept_22_1_3_9_1_9082 1 135 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 135 163))))))))))))))))))))))))))))) (allB_succ' 30 134 163 (Eq.refl Bool.true) (allA_of_3_1 30
  134 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 133 163 (Eq.refl Bool.true) (allA_succ_of_accept 30
  133 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 133 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 133 163 (accept_3_3 29 133 163 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 133 163 (Polychromatic418967fa.accept_20_8_13_3_1_9081 28 133 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 133 163 (Polychromatic418967fa.accept_13_1_3_7_1_1710 27 133
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 133 163 (accept_3_3 26 133
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 133 163
  (Polychromatic418967fa.accept_21_4_7_16_1_2938 25 133 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 133 163 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 133 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 133 163 (accept_3_3 23 133 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 133 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 133 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 133 163 (Polychromatic418967fa.accept_9_3_7_1_1_143
  21 133 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 133 163 (accept_3_3 20
  133 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 133 163
  (Polychromatic418967fa.accept_14_5_7_9_1_3828 19 133 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 133 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 133 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 133 163 (accept_3_3 17 133 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 133 163 (Polychromatic418967fa.accept_14_2_7_9_1_2937 16 133 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 133 163
  (Polychromatic418967fa.accept_9_6_7_1_1_145 15 133 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 133 163 (accept_3_3 14 133 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 133 163 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 133 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 133 163 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 133 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 133 163 (accept_3_3 11 133 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 133 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 133 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 133 163
  (Polychromatic418967fa.accept_13_9_3_7_1_1065 9 133 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 133 163 (accept_3_3 8 133 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  133 163 (Polychromatic418967fa.accept_17_7_14_10_1_1846 7 133 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 133 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 133 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 133 163 (accept_3_3 5 133 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 133 163 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 133 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 133 163
  (Polychromatic418967fa.accept_9_3_7_1_1_143 3 133 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 133 163 (accept_3_3 2 133 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  133 163 (Polychromatic418967fa.accept_13_1_3_7_1_1710 1 133 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 133 163))))))))))))))))))))))))))))))) (allB_succ' 32 132 163 (Eq.refl Bool.true)
  (allA_succ_of_accept 31 132 163 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 132 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 132 163 (Polychromatic418967fa.accept_9_3_6_1_1_24 30 132 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 132 163 (accept_3_3 29 132 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 132 163
  (Polychromatic418967fa.accept_16_12_4_3_1_4295 28 132 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 132 163 (Polychromatic418967fa.accept_18_9_6_1_1_3687 27 132 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 132 163 (accept_3_3 26 132 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 132 163 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 132 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 132 163 (Polychromatic418967fa.accept_7_3_6_2_1_90 24
  132 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 132 163 (accept_3_3 23
  132 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 132 163
  (Polychromatic418967fa.accept_7_1_6_2_1_18 22 132 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 132 163 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 132 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 132 163 (accept_3_3 20 132 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 132 163 (Polychromatic418967fa.accept_23_19_17_2_1_9080 19 132 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 132 163
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 132 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 132 163 (accept_3_3 17 132 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 132 163 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 132 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 132 163 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 132 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 132 163 (accept_3_3 14 132 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 132 163 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 132 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 132 163
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 132 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 132 163 (accept_3_3 11 132 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 132 163 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 132 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 132 163 (Polychromatic418967fa.accept_13_9_2_7_1_1083 9 132 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 132 163 (accept_3_3 8 132 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 132 163 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 132 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 132 163
  (Polychromatic418967fa.accept_16_6_4_3_1_2189 6 132 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 132 163 (accept_3_3 5 132 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  132 163 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 132 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 132 163 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 132 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 132 163 (accept_3_3 2 132 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 132 163 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 132 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132 163)))))))))))))))))))))))))))))))) (allB_succ' 33
  131 163 (Eq.refl Bool.true) (allA_of_3_1 33 131 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 130 163
  (Eq.refl Bool.true) (allA_succ_of_accept 33 130 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 130 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 130 163 (accept_3_3 32 130 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 130 163 (Polychromatic418967fa.accept_15_1_10_13_1_939 31 130
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 130 163
  (Polychromatic418967fa.accept_9_3_4_1_1_22 30 130 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 130 163 (accept_3_3 29 130 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 130 163 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 130 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 130 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 130 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 130 163 (accept_3_3 26 130 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 130 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 130 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 130 163
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 130 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 130 163 (accept_3_3 23 130 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 130 163 (Polychromatic418967fa.accept_16_6_2_3_1_4223 22 130 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 130 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 130 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 130 163 (accept_3_3 20 130 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 130 163 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 130 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 130 163
  (Polychromatic418967fa.accept_15_3_10_13_1_2605 18 130 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 130 163 (accept_3_3 17 130 163 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 130 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 130 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 130 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 130 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 130 163 (accept_3_3 14 130 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 130 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 13
  130 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 130 163
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 130 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 130 163 (accept_3_3 11 130 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 130 163 (Polychromatic418967fa.accept_21_10_4_16_1_9079 10 130 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 130 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 130 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 130 163 (accept_3_3 8 130 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 130 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 130 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 130 163
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 130 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 130 163 (accept_3_3 5 130 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  130 163 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 130 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 130 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 130 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 130 163 (accept_3_3 2 130 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 130 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 130 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 130 163)))))))))))))))))))))))))))))))))) (allB_succ' 35
  129 163 (Eq.refl Bool.true) (allA_succ_of_accept 34 129 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 129 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 129 163
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 129 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 129 163 (accept_3_3 32 129 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 129 163 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 129 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 129 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 129 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 129 163 (accept_3_3 29 129 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 129 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 129 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 129 163
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 129 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 129 163 (accept_3_3 26 129 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 129 163 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 129 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 129 163 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 129 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 129 163 (accept_3_3 23 129 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 129 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 129 163
  (Polychromatic418967fa.accept_11_10_8_9_1_492 21 129 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 129 163 (accept_3_3 20 129 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 129 163 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 129 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 129 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 129 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 129 163 (accept_3_3 17 129 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 129 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 129 163
  (Polychromatic418967fa.accept_7_1_3_2_1_13 15 129 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 129 163 (accept_3_3 14 129 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 129 163 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 129 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 129 163 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 129 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 129 163 (accept_3_3 11 129 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 129 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 129 163
  (Polychromatic418967fa.accept_18_9_3_1_1_2559 9 129 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 129 163 (accept_3_3 8 129 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  129 163 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 129 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 129 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 129 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 129 163 (accept_3_3 5 129 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 129 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 129 163
  (Polychromatic418967fa.accept_12_3_9_7_1_472 3 129 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 129 163 (accept_3_3 2 129 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  129 163 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 129 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 129 163))))))))))))))))))))))))))))))))))) (allB_succ' 36 128 163 (Eq.refl Bool.true)
  (allA_of_3_1 36 128 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 127 163 (Eq.refl Bool.true)
  (allA_succ_of_accept 36 127 163 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 127 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 127 163 (accept_3_3 35 127 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 127 163 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 127 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 127 163
  (Polychromatic418967fa.accept_22_11_17_9_1_1380 33 127 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 127 163 (accept_3_3 32 127 163 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 127 163 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 127 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 127 163 (Polychromatic418967fa.accept_13_4_10_7_1_1701 30 127
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 127 163 (accept_3_3 29 127
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 127 163
  (Polychromatic418967fa.accept_8_4_7_3_1_144 28 127 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 127 163 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 127 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 127 163 (accept_3_3 26 127 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 127 163 (Polychromatic418967fa.accept_10_5_7_3_1_561 25 127 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 127 163
  (Polychromatic418967fa.accept_7_3_1_2_1_247 24 127 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 127 163 (accept_3_3 23 127 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 127 163 (Polychromatic418967fa.accept_14_8_1_9_1_2085 22 127 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 127 163 (Polychromatic418967fa.accept_13_8_10_7_1_1702 21 127 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 127 163 (accept_3_3 20 127 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 127 163 (Polychromatic418967fa.accept_17_2_8_10_1_2870 19 127
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 127 163
  (Polychromatic418967fa.accept_16_2_15_3_1_1300 18 127 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 127 163 (accept_3_3 17 127 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 127 163 (Polychromatic418967fa.accept_10_6_7_3_1_547 16 127 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 127 163 (Polychromatic418967fa.accept_10_5_7_3_1_561 15 127 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 127 163 (accept_3_3 14 127 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 127 163 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 127 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 127 163
  (Polychromatic418967fa.accept_8_4_7_3_1_144 12 127 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 127 163 (accept_3_3 11 127 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 127 163 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 127 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 127 163 (Polychromatic418967fa.accept_15_9_7_13_1_1664 9 127 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 127 163 (accept_3_3 8 127 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 127 163 (Polychromatic418967fa.accept_16_7_15_3_1_1302 7 127
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 127 163
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 127 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 127 163 (accept_3_3 5 127 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  127 163 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 127 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 127 163 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 127 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 127 163 (accept_3_3 2 127 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 127 163 (Polychromatic418967fa.accept_24_1_7_19_1_917 1 127 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 127 163))))))))))))))))))))))))))))))))))))) (allB_succ'
  38 126 163 (Eq.refl Bool.true) (allA_succ_of_accept 37 126 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 126 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 126 163
  (Polychromatic418967fa.accept_23_13_11_2_1_3894 36 126 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 126 163 (accept_3_3 35 126 163 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 126 163 (Polychromatic418967fa.accept_13_8_9_7_1_530 34 126 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 126 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 126 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 126 163 (accept_3_3 32 126 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 126 163
  (Polychromatic418967fa.accept_17_14_7_10_1_7808 31 126 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 126 163 (Polychromatic418967fa.accept_13_4_9_7_1_2402 30 126 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 126 163 (accept_3_3 29 126 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 126 163 (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 126
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 126 163
  (Polychromatic418967fa.accept_10_7_6_3_1_927 27 126 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 126 163 (accept_3_3 26 126 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 126 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 126 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 126 163 (Polychromatic418967fa.accept_13_11_9_7_1_2484 24 126 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 126 163 (accept_3_3 23 126 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 126 163 (Polychromatic418967fa.accept_15_7_6_13_1_936 22 126
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 126 163
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 126 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 126 163 (accept_3_3 20 126 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 126 163 (Polychromatic418967fa.accept_10_9_6_3_1_545 19 126 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 126 163 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 126 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 126 163 (accept_3_3 17 126 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 126 163 (Polychromatic418967fa.accept_13_3_9_7_1_1730 16 126
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 126 163
  (Polychromatic418967fa.accept_13_2_9_7_1_164 15 126 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 126 163 (accept_3_3 14 126 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 126 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 126 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 126 163 (Polychromatic418967fa.accept_24_12_6_19_1_7180 12 126 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 126 163 (accept_3_3 11 126 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 126 163 (Polychromatic418967fa.accept_19_10_12_11_1_7622 10
  126 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 126 163
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 126 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 126 163 (accept_3_3 8 126 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  126 163 (Polychromatic418967fa.accept_10_7_6_3_1_927 7 126 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 126 163 (Polychromatic418967fa.accept_13_6_9_7_1_2430 6 126 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 126 163 (accept_3_3 5 126 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 126 163 (Polychromatic418967fa.accept_13_4_9_7_1_2402 4 126 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 126 163
  (Polychromatic418967fa.accept_13_3_9_7_1_1730 3 126 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 126 163 (accept_3_3 2 126 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  126 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 126 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 126 163)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 125 163 (Eq.refl Bool.true)
  (allA_of_3_1 39 125 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 40 124 163 (Eq.refl Bool.true)
  (allA_succ_of_accept 39 124 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 124 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 124 163 (accept_3_3 38 124 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 124 163 (Polychromatic418967fa.accept_10_7_4_3_1_560 37 124 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 124 163
  (Polychromatic418967fa.accept_15_6_4_13_1_403 36 124 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 124 163 (accept_3_3 35 124 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 124 163 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 124 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 124 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 124 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 124 163 (accept_3_3 32 124 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 124 163 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 124 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 124 163
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 124 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 124 163 (accept_3_3 29 124 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 124 163 (Polychromatic418967fa.accept_11_6_3_9_1_906 28 124 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 124 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 124 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 124 163 (accept_3_3 26 124 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 124 163 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 124 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 124 163
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 124 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 124 163 (accept_3_3 23 124 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 124 163 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 124 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 124 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 124 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 124 163 (accept_3_3 20 124 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 124 163 (Polychromatic418967fa.accept_10_9_4_3_1_539 19 124 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 124 163
  (Polychromatic418967fa.accept_7_4_5_2_1_243 18 124 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 124 163 (accept_3_3 17 124 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 124 163 (Polychromatic418967fa.accept_23_16_9_2_1_9078 16 124 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 124 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 124 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 124 163 (accept_3_3 14 124 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 124 163 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 124 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 124 163
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 124 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 124 163 (accept_3_3 11 124 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 124 163 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 124 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 124 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 124 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 124 163 (accept_3_3 8 124 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 124 163 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 124 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 124 163
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 124 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 124 163 (accept_3_3 5 124 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  124 163 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 124 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 124 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 124 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 124 163 (accept_3_3 2 124 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 124 163 (Polychromatic418967fa.accept_19_1_10_11_1_4721 1 124 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 124 163))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 41 123 163 (Eq.refl Bool.true) (allA_succ_of_accept 40 123 163 (Polychromatic418967fa.accept_6_4_3_1_1_57
  40 123 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 123 163
  (Polychromatic418967fa.accept_9_3_6_1_1_24 39 123 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 123 163 (accept_3_3 38 123 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 123 163 (Polychromatic418967fa.accept_11_4_2_9_1_496 37 123 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 123 163 (Polychromatic418967fa.accept_19_17_9_11_1_6057 36 123 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 123 163 (accept_3_3 35 123 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 123 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 123 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 123 163
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 123 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 123 163 (accept_3_3 32 123 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 123 163 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 123 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 123 163 (Polychromatic418967fa.accept_9_3_6_1_1_24 30 123 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 123 163 (accept_3_3 29 123 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 123 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 123 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 123 163
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 123 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 123 163 (accept_3_3 26 123 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 123 163 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 123 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 123 163 (Polychromatic418967fa.accept_15_9_3_13_1_1686 24 123 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 123 163 (accept_3_3 23 123 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 123 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 123 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 123 163
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 123 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 123 163 (accept_3_3 20 123 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 123 163 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 123 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 123 163 (Polychromatic418967fa.accept_11_7_2_9_1_480 18 123 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 123 163 (accept_3_3 17 123 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 123 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 123 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 123 163
  (Polychromatic418967fa.accept_11_4_2_9_1_496 15 123 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 123 163 (accept_3_3 14 123 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 123 163 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 123 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 123 163 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 123 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 123 163 (accept_3_3 11 123 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 123 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 123 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 123 163
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 123 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 123 163 (accept_3_3 8 123 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  123 163 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 123 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 123 163 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 123 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 123 163 (accept_3_3 5 123 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 123 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 123 163
  (Polychromatic418967fa.accept_9_3_6_1_1_24 3 123 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 123 163 (accept_3_3 2 123 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  123 163 (Polychromatic418967fa.accept_13_1_6_7_1_550 1 123 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 123 163))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 122 163 (Eq.refl Bool.true)
  (allA_of_3_1 42 122 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 121 163 (Eq.refl Bool.true)
  (allA_succ_of_accept 42 121 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 121 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 121 163 (accept_3_3 41 121 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 121 163 (Polychromatic418967fa.accept_15_10_1_13_1_2609 40 121 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 121 163
  (Polychromatic418967fa.accept_9_3_4_1_1_22 39 121 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 121 163 (accept_3_3 38 121 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 121 163 (Polychromatic418967fa.accept_13_11_4_7_1_2419 37 121 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 121 163 (Polychromatic418967fa.accept_13_10_4_7_1_2465 36 121 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 121 163 (accept_3_3 35 121 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 121 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 121 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 121 163
  (Polychromatic418967fa.accept_9_6_4_1_1_390 33 121 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 121 163 (accept_3_3 32 121 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 121 163 (Polychromatic418967fa.accept_19_12_7_11_1_7658 31 121 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 121 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 121 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 121 163 (accept_3_3 29 121 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 121 163 (Polychromatic418967fa.accept_10_8_1_3_1_1374 28 121 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 121 163
  (Polychromatic418967fa.accept_15_12_1_13_1_3444 27 121 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 121 163 (accept_3_3 26 121 163 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 121 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 121 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 121 163 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 121 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 121 163 (accept_3_3 23 121 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 121 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 22
  121 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 121 163
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 121 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 121 163 (accept_3_3 20 121 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 121 163 (Polychromatic418967fa.accept_13_6_4_7_1_2464 19 121 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 121 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 121 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 121 163 (accept_3_3 17 121 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 121 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 121 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 121 163
  (Polychromatic418967fa.accept_9_6_4_1_1_390 15 121 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 121 163 (accept_3_3 14 121 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 121 163 (Polychromatic418967fa.accept_19_13_7_11_1_7551 13 121 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 121 163 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 121 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 121 163 (accept_3_3 11 121 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 121 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 121 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 121 163
  (Polychromatic418967fa.accept_13_9_4_7_1_1694 9 121 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 121 163 (accept_3_3 8 121 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  121 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 121 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 121 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 121 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 121 163 (accept_3_3 5 121 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 121 163 (Polychromatic418967fa.accept_19_4_7_11_1_6056 4 121 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 121 163
  (Polychromatic418967fa.accept_9_3_4_1_1_22 3 121 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 121 163 (accept_3_3 2 121 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  121 163 (Polychromatic418967fa.accept_23_1_6_2_1_9077 1 121 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 121 163))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 120 163 (Eq.refl Bool.true)
  (allA_succ_of_accept 43 120 163 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 120 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 120 163 (Polychromatic418967fa.accept_9_6_3_1_1_155 42 120 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 120 163 (accept_3_3 41 120 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 120 163 (Polychromatic418967fa.accept_9_4_3_1_1_154
  40 120 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 120 163
  (Polychromatic418967fa.accept_18_3_12_1_1_3787 39 120 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 120 163 (accept_3_3 38 120 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 120 163 (Polychromatic418967fa.accept_13_11_3_7_1_2513 37 120 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 120 163 (Polychromatic418967fa.accept_13_10_3_7_1_2517 36 120 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 120 163 (accept_3_3 35 120 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 120 163 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 120 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 120 163
  (Polychromatic418967fa.accept_9_6_3_1_1_155 33 120 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 120 163 (accept_3_3 32 120 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 120 163 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 120 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 120 163 (Polychromatic418967fa.accept_11_8_10_9_1_1401 30 120 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 120 163 (accept_3_3 29 120 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 120 163 (Polychromatic418967fa.accept_16_12_8_3_1_4241 28 120
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 120 163
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 120 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 120 163 (accept_3_3 26 120 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 120 163 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 120 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 120 163 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 120 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 120 163 (accept_3_3 23 120 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 120 163 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 120 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 120 163
  (Polychromatic418967fa.accept_13_8_3_7_1_2455 21 120 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 120 163 (accept_3_3 20 120 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 120 163 (Polychromatic418967fa.accept_11_8_10_9_1_1401 19 120 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 120 163 (Polychromatic418967fa.accept_19_18_6_11_1_7696 18 120 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 120 163 (accept_3_3 17 120 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 120 163 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 120 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 120 163
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 120 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 120 163 (accept_3_3 14 120 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 120 163 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 120 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 120 163 (Polychromatic418967fa.accept_11_1_10_9_1_871 12 120 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 120 163 (accept_3_3 11 120 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 120 163 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 120 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 120 163
  (Polychromatic418967fa.accept_13_9_3_7_1_1065 9 120 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 120 163 (accept_3_3 8 120 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  120 163 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 120 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 120 163 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 120 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 120 163 (accept_3_3 5 120 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 120 163 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 120 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 120 163
  (Polychromatic418967fa.accept_7_3_1_2_1_247 3 120 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 120 163 (accept_3_3 2 120 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  120 163 (Polychromatic418967fa.accept_11_1_10_9_1_871 1 120 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 120 163)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 119 163 (Eq.refl Bool.true)
  (allA_of_3_1 45 119 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 46 118 163 (Eq.refl Bool.true)
  (allA_succ_of_accept 45 118 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 118 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 118 163 (accept_3_3 44 118 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 118 163 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 118 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 118 163 (Polychromatic418967fa.accept_13_3_1_7_1_1706
  42 118 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 118 163 (accept_3_3 41
  118 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 118 163
  (Polychromatic418967fa.accept_12_4_10_7_1_149 40 118 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 118 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 118 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 118 163 (accept_3_3 38 118 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 118 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 118 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 118 163 (Polychromatic418967fa.accept_7_1_6_2_1_18 36
  118 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 118 163 (accept_3_3 35
  118 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 118 163
  (Polychromatic418967fa.accept_13_8_1_7_1_2505 34 118 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 118 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 118 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 118 163 (accept_3_3 32 118 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 118 163 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 118 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 118 163
  (Polychromatic418967fa.accept_21_9_13_16_1_2914 30 118 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 118 163 (accept_3_3 29 118 163 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 118 163 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 118 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 118 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 118 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 118 163 (accept_3_3 26 118 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 118 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 25
  118 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 118 163
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 118 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 118 163 (accept_3_3 23 118 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 118 163 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 118 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 118 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 118 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 118 163 (accept_3_3 20 118 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 118 163 (Polychromatic418967fa.accept_13_6_1_7_1_1690 19 118 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 118 163
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 118 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 118 163 (accept_3_3 17 118 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 118 163 (Polychromatic418967fa.accept_10_6_8_3_1_930 16 118 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 118 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 118 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 118 163 (accept_3_3 14 118 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 118 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 118 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 118 163
  (Polychromatic418967fa.accept_19_12_4_11_1_6078 12 118 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 118 163 (accept_3_3 11 118 163 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 118 163 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 118 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 118 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 118 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 118 163 (accept_3_3 8 118 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 118 163
  (Polychromatic418967fa.accept_17_7_16_10_1_1849 7 118 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 118 163 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 118 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 118 163 (accept_3_3 5 118 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 118 163 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 118 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 118 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 3
  118 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 118 163 (accept_3_3 2 118
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 118 163 (Polychromatic418967fa.accept_4_1_2_3_1_9
  1 118 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118
  163)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 117 163 (Eq.refl Bool.true) (allA_succ_of_accept 46
  117 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 117 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 117 163 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 117 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 117 163 (accept_3_3 44 117 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 163 (Polychromatic418967fa.accept_25_18_17_13_1_9076 43 117 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 117 163
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 117 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 117 163 (accept_3_3 41 117 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 117 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 117 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 117 163 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 117 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 117 163 (accept_3_3 38 117 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 163 (Polychromatic418967fa.accept_19_18_3_11_1_6066 37 117 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 117 163
  (Polychromatic418967fa.accept_10_6_7_3_1_547 36 117 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 117 163 (accept_3_3 35 117 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 117 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 117 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 117 163 (Polychromatic418967fa.accept_15_3_12_13_1_2549 33 117 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 117 163 (accept_3_3 32 117 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 163 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 117 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 117 163
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 117 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 117 163 (accept_3_3 29 117 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 117 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 117 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 117 163 (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 117 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 117 163 (accept_3_3 26 117 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 163 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 117 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 117 163
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 117 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 117 163 (accept_3_3 23 117 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 117 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 117 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 117 163 (Polychromatic418967fa.accept_14_7_5_9_1_2911 21 117 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 117 163 (accept_3_3 20 117 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 163 (Polychromatic418967fa.accept_17_2_15_10_1_5171 19 117
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 117 163
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 117 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 117 163 (accept_3_3 17 117 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 117 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 117 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 117 163 (Polychromatic418967fa.accept_10_5_7_3_1_561 15 117 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 163 (accept_3_3 14 117 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 163 (Polychromatic418967fa.accept_11_2_7_9_1_890 13 117
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 117 163
  (Polychromatic418967fa.accept_19_12_3_11_1_9075 12 117 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 117 163 (accept_3_3 11 117 163 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 117 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 117 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 163 (Polychromatic418967fa.accept_19_9_3_11_1_7505 9 117
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 163 (accept_3_3 8 117 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 163 (Polychromatic418967fa.accept_14_7_5_9_1_2911
  7 117 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 163
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 117 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 117 163 (accept_3_3 5 117 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  117 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 117 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 117 163 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 117 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 163 (accept_3_3 2 117 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 163 (Polychromatic418967fa.accept_15_1_12_13_1_944 1 117 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117 163)))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 48 116 163 (Eq.refl Bool.true) (allA_of_3_1 48 116 163 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 49 115 163 (Eq.refl Bool.true) (allA_succ_of_accept 48 115 163 (Polychromatic418967fa.accept_7_6_3_2_1_461
  48 115 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 115 163 (accept_3_3 47
  115 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 115 163
  (Polychromatic418967fa.accept_15_1_10_13_1_939 46 115 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 115 163 (Polychromatic418967fa.accept_20_5_15_3_1_4516 45 115 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 115 163 (accept_3_3 44 115 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 115 163 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 115 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 115 163 (Polychromatic418967fa.accept_9_6_7_1_1_145
  42 115 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 115 163 (accept_3_3 41
  115 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 115 163
  (Polychromatic418967fa.accept_7_5_3_2_1_249 40 115 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 115 163 (Polychromatic418967fa.accept_9_3_7_1_1_143 39 115 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 115 163 (accept_3_3 38 115 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 115 163 (Polychromatic418967fa.accept_10_7_5_3_1_542 37 115 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 115 163
  (Polychromatic418967fa.accept_7_1_3_2_1_13 36 115 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 115 163 (accept_3_3 35 115 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 115 163 (Polychromatic418967fa.accept_7_6_3_2_1_461 34 115 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 115 163 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 115 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 115 163 (accept_3_3 32 115 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 115 163 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 115 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 115 163
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 115 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 115 163 (accept_3_3 29 115 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 115 163 (Polychromatic418967fa.accept_10_8_5_3_1_543 28 115 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 115 163 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 115 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 115 163 (accept_3_3 26 115 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 115 163 (Polychromatic418967fa.accept_13_12_11_7_1_2491 25 115 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 115 163
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 115 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 115 163 (accept_3_3 23 115 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 115 163 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 115 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 115 163 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 115 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 115 163 (accept_3_3 20 115 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 115 163 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 115 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 115 163
  (Polychromatic418967fa.accept_10_8_5_3_1_543 18 115 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 115 163 (accept_3_3 17 115 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 115 163 (Polychromatic418967fa.accept_13_3_11_7_1_2488 16 115 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 115 163 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 115 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 115 163 (accept_3_3 14 115 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 115 163 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 115 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 115 163
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 115 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 115 163 (accept_3_3 11 115 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 115 163 (Polychromatic418967fa.accept_19_10_1_11_1_7532 10 115 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 115 163 (Polychromatic418967fa.accept_13_9_11_7_1_1077 9 115 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 115 163 (accept_3_3 8 115 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 115 163 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 115 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 115 163
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 115 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 115 163 (accept_3_3 5 115 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  115 163 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 115 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 115 163 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 115 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 163 (accept_3_3 2 115 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 115 163 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 115 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115 163)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 50 114 163 (Eq.refl Bool.true) (allA_succ_of_accept 49 114 163 (Polychromatic418967fa.accept_4_1_2_3_1_9
  49 114 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 114 163
  (Polychromatic418967fa.accept_9_3_6_1_1_24 48 114 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 114 163 (accept_3_3 47 114 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 114 163 (Polychromatic418967fa.accept_11_2_4_9_1_484 46 114 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 114 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 114 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 114 163 (accept_3_3 44 114 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 114 163 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 114 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 114 163
  (Polychromatic418967fa.accept_13_3_10_7_1_1061 42 114 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 114 163 (accept_3_3 41 114 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 114 163 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 114 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 114 163 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 114 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 114 163 (accept_3_3 38 114 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 114 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 114 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 114 163
  (Polychromatic418967fa.accept_17_2_12_10_1_9034 36 114 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 114 163 (accept_3_3 35 114 163 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 114 163 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 114 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 114 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 114 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 114 163 (accept_3_3 32 114 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 114 163 (Polychromatic418967fa.accept_9_4_6_1_1_393
  31 114 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 114 163
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 114 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 114 163 (accept_3_3 29 114 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 114 163 (Polychromatic418967fa.accept_20_8_14_3_1_9074 28 114 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 114 163 (Polychromatic418967fa.accept_10_7_4_3_1_560 27 114 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 114 163 (accept_3_3 26 114 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 114 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 114 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 114 163
  (Polychromatic418967fa.accept_11_2_4_9_1_484 24 114 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 114 163 (accept_3_3 23 114 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 114 163 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 114 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 114 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 114 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 114 163 (accept_3_3 20 114 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 114 163 (Polychromatic418967fa.accept_10_9_4_3_1_539 19 114 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 114 163
  (Polychromatic418967fa.accept_14_4_2_9_1_2092 18 114 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 114 163 (accept_3_3 17 114 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 114 163 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 114 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 114 163 (Polychromatic418967fa.accept_16_15_2_3_1_4262 15 114 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 114 163 (accept_3_3 14 114 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 114 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 114 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 114 163
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 114 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 114 163 (accept_3_3 11 114 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 114 163 (Polychromatic418967fa.accept_21_10_9_16_1_9073 10 114 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 114 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 114 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 114 163 (accept_3_3 8 114 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 114 163 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 114 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 114 163
  (Polychromatic418967fa.accept_16_6_2_3_1_4223 6 114 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 114 163 (accept_3_3 5 114 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  114 163 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 114 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 114 163 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 114 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 114 163 (accept_3_3 2 114 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 114 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 114 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  163)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 113 163 (Eq.refl Bool.true) (allA_of_3_1 51 113
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 52 112 163 (Eq.refl Bool.true) (allA_succ_of_accept 51 112
  163 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 112 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 112 163 (accept_3_3 50 112 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 112 163 (Polychromatic418967fa.accept_13_10_8_7_1_1074 49 112 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 112 163 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 112 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 112 163 (accept_3_3 47 112 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 112 163 (Polychromatic418967fa.accept_12_10_4_7_1_948 46 112 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 112 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 112 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 112 163 (accept_3_3 44 112 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 112 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 112 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 112 163 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 112 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 112 163 (accept_3_3 41 112 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 112 163 (Polychromatic418967fa.accept_11_7_2_9_1_480 40 112 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 112 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 112 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 112 163 (accept_3_3 38 112 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 112 163 (Polychromatic418967fa.accept_11_4_2_9_1_496 37 112 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 112 163 (Polychromatic418967fa.accept_13_10_8_7_1_1074 36 112 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 112 163 (accept_3_3 35 112 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 112 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 112 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 112 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 112 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 112 163 (accept_3_3 32 112 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 112 163 (Polychromatic418967fa.accept_10_1_2_3_1_1910 31 112 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 112 163 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 112 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 112 163 (accept_3_3 29 112 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 112 163 (Polychromatic418967fa.accept_13_2_8_7_1_2424 28 112 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 112 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 112 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 112 163 (accept_3_3 26 112 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 112 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 112 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 112 163 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 112 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 112 163 (accept_3_3 23 112 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 112 163 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 112 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 112 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 112 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 112 163 (accept_3_3 20 112 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 112 163 (Polychromatic418967fa.accept_27_19_4_1_1_9072 19 112 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 112 163 (Polychromatic418967fa.accept_11_7_2_9_1_480 18 112 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 112 163 (accept_3_3 17 112 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 112 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 112 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 112 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 112 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 112 163 (accept_3_3 14 112 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 112 163 (Polychromatic418967fa.accept_19_13_17_11_1_4716 13 112 163 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 112 163 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 112 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 112 163 (accept_3_3 11 112 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 112 163 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 112
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 112 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 112 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 112 163 (accept_3_3 8 112 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  112 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 112 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 112 163 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 112 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 112 163 (accept_3_3 5 112 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 112 163 (Polychromatic418967fa.accept_11_4_2_9_1_496 4 112 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 112 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 112 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 112 163 (accept_3_3 2 112 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  112 163 (Polychromatic418967fa.accept_10_1_2_3_1_1910 1 112 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 112 163)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 111 163 (Eq.refl
  Bool.true) (allA_succ_of_accept 52 111 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 111 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 111 163 (Polychromatic418967fa.accept_9_6_3_1_1_155
  51 111 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 111 163 (accept_3_3 50
  111 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 163
  (Polychromatic418967fa.accept_9_4_3_1_1_154 49 111 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 111 163 (Polychromatic418967fa.accept_10_8_1_3_1_1374 48 111 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 111 163 (accept_3_3 47 111 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 111 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 111 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 111 163 (Polychromatic418967fa.accept_7_3_6_2_1_90 45
  111 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 111 163 (accept_3_3 44
  111 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 163
  (Polychromatic418967fa.accept_7_1_6_2_1_18 43 111 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 111 163 (Polychromatic418967fa.accept_9_6_3_1_1_155 42 111 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 111 163 (accept_3_3 41 111 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 111 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 111 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 111 163 (Polychromatic418967fa.accept_7_4_6_2_1_451
  39 111 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 111 163 (accept_3_3 38
  111 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 163
  (Polychromatic418967fa.accept_15_7_6_13_1_936 37 111 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 111 163 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 111 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 111 163 (accept_3_3 35 111 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 111 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 111 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 111 163 (Polychromatic418967fa.accept_9_6_3_1_1_155
  33 111 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 111 163 (accept_3_3 32
  111 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 163
  (Polychromatic418967fa.accept_7_3_6_2_1_90 31 111 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 111 163 (Polychromatic418967fa.accept_17_13_9_10_1_2888 30 111 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 111 163 (accept_3_3 29 111 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 111 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 111 163
  (Polychromatic418967fa.accept_16_11_15_3_1_1304 27 111 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 111 163 (accept_3_3 26 111 163 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 111 163 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 111 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 163 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 111 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 111 163 (accept_3_3 23 111 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 111 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 22
  111 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 111 163
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 21 111 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 111 163 (accept_3_3 20 111 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 111 163 (Polychromatic418967fa.accept_15_4_6_13_1_956 19 111 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 111 163 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 111 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 163 (accept_3_3 17 111 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 111 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 111 163
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 111 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 111 163 (accept_3_3 14 111 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 111 163 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 111 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 111 163 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 111 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 163 (accept_3_3 11 111 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 111 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 111 163
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 111 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 111 163 (accept_3_3 8 111 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  111 163 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 111 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 111 163 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 111 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 163 (accept_3_3 5 111 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 111 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 111 163
  (Polychromatic418967fa.accept_7_3_6_2_1_90 3 111 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 111 163 (accept_3_3 2 111 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  111 163 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 111 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 111 163))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 110 163 (Eq.refl
  Bool.true) (allA_of_3_1 54 110 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 55 109 163 (Eq.refl Bool.true)
  (allA_succ_of_accept 54 109 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 109 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 109 163 (accept_3_3 53 109 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 109 163 (Polychromatic418967fa.accept_11_8_10_9_1_1401 52 109 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 109 163
  (Polychromatic418967fa.accept_13_12_5_7_1_1696 51 109 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 109 163 (accept_3_3 50 109 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 109 163 (Polychromatic418967fa.accept_16_1_13_3_1_2168 49 109 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 109 163 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 109 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 109 163 (accept_3_3 47 109 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 109 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 109 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 109 163
  (Polychromatic418967fa.accept_11_1_10_9_1_871 45 109 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 109 163 (accept_3_3 44 109 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 109 163 (Polychromatic418967fa.accept_19_5_14_11_1_6084 43 109 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 109 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 109 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 109 163 (accept_3_3 41 109 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 109 163 (Polychromatic418967fa.accept_7_5_4_2_1_235 40 109 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 109 163
  (Polychromatic418967fa.accept_15_9_4_13_1_4482 39 109 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 109 163 (accept_3_3 38 109 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 109 163 (Polychromatic418967fa.accept_13_11_5_7_1_2420 37 109 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 109 163 (Polychromatic418967fa.accept_10_6_9_3_1_935 36 109 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 109 163 (accept_3_3 35 109 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 109 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 109 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 109 163
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 109 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 109 163 (accept_3_3 32 109 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 109 163 (Polychromatic418967fa.accept_16_15_13_3_1_4215 31 109 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 109 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 109 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 109 163 (accept_3_3 29 109 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 109 163 (Polychromatic418967fa.accept_13_2_5_7_1_1695 28 109 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 109 163
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 109 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 109 163 (accept_3_3 26 109 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 109 163 (Polychromatic418967fa.accept_13_12_5_7_1_1696 25 109 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 109 163 (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 109 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 109 163 (accept_3_3 23 109 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 109 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 109 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 109 163
  (Polychromatic418967fa.accept_15_6_4_13_1_403 21 109 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 109 163 (accept_3_3 20 109 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 109 163 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 109 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 109 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 109 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 109 163 (accept_3_3 17 109 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 109 163 (Polychromatic418967fa.accept_10_6_9_3_1_935 16 109 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 109 163
  (Polychromatic418967fa.accept_13_2_5_7_1_1695 15 109 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 109 163 (accept_3_3 14 109 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 109 163 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 109 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 109 163 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 109 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 109 163 (accept_3_3 11 109 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 109 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 109 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 109 163
  (Polychromatic418967fa.accept_15_9_4_13_1_4482 9 109 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 109 163 (accept_3_3 8 109 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  109 163 (Polychromatic418967fa.accept_19_7_14_11_1_4724 7 109 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 109 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 109 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 109 163 (accept_3_3 5 109 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 109 163 (Polychromatic418967fa.accept_10_4_9_3_1_1907 4 109 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 109 163
  (Polychromatic418967fa.accept_17_3_7_10_1_3948 3 109 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 109 163 (accept_3_3 2 109 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  109 163 (Polychromatic418967fa.accept_11_1_10_9_1_871 1 109 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 109 163))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 108 163 (Eq.refl
  Bool.true) (allA_succ_of_accept 55 108 163 (Polychromatic418967fa.accept_7_6_3_2_1_461 55 108 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 108 163 (Polychromatic418967fa.accept_7_5_3_2_1_249
  54 108 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 108 163 (accept_3_3 53
  108 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 108 163
  (Polychromatic418967fa.accept_16_4_12_3_1_2180 52 108 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 108 163 (Polychromatic418967fa.accept_10_1_8_3_1_947 51 108 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 108 163 (accept_3_3 50 108 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 108 163 (Polychromatic418967fa.accept_13_10_4_7_1_2465 49 108 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 108 163
  (Polychromatic418967fa.accept_7_6_3_2_1_461 48 108 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 108 163 (accept_3_3 47 108 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 108 163 (Polychromatic418967fa.accept_10_6_8_3_1_930 46 108 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 108 163 (Polychromatic418967fa.accept_10_5_8_3_1_229 45 108 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 108 163 (accept_3_3 44 108 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 108 163 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 108 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 108 163
  (Polychromatic418967fa.accept_13_3_4_7_1_1711 42 108 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 108 163 (accept_3_3 41 108 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 108 163 (Polychromatic418967fa.accept_7_5_3_2_1_249 40 108 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 108 163 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 108 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 108 163 (accept_3_3 38 108 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 108 163 (Polychromatic418967fa.accept_13_11_4_7_1_2419 37 108 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 108 163
  (Polychromatic418967fa.accept_7_1_3_2_1_13 36 108 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 108 163 (accept_3_3 35 108 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 108 163 (Polychromatic418967fa.accept_7_6_3_2_1_461 34 108 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 108 163 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 108 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 108 163 (accept_3_3 32 108 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 108 163 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 108 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 108 163
  (Polychromatic418967fa.accept_21_9_3_16_1_1684 30 108 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 108 163 (accept_3_3 29 108 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 108 163 (Polychromatic418967fa.accept_21_7_3_16_1_7337 28 108 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 108 163 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 108 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 108 163 (accept_3_3 26 108 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 108 163 (Polychromatic418967fa.accept_10_5_8_3_1_229 25 108 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 108 163
  (Polychromatic418967fa.accept_13_11_4_7_1_2419 24 108 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 108 163 (accept_3_3 23 108 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 108 163 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 108 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 108 163 (Polychromatic418967fa.accept_10_1_8_3_1_947 21 108 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 108 163 (accept_3_3 20 108 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 108 163 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 108 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 108 163
  (Polychromatic418967fa.accept_20_18_8_3_1_9071 18 108 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 108 163 (accept_3_3 17 108 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 108 163 (Polychromatic418967fa.accept_10_6_8_3_1_930 16 108 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 108 163 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 108 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 108 163 (accept_3_3 14 108 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 108 163 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 108 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 108 163
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 108 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 108 163 (accept_3_3 11 108 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 108 163 (Polychromatic418967fa.accept_13_10_4_7_1_2465 10 108 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 108 163 (Polychromatic418967fa.accept_13_9_4_7_1_1694 9 108 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 108 163 (accept_3_3 8 108 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 108 163 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 108 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 108 163
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 108 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 108 163 (accept_3_3 5 108 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  108 163 (Polychromatic418967fa.accept_16_4_12_3_1_2180 4 108 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 108 163 (Polychromatic418967fa.accept_13_3_4_7_1_1711 3 108 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 108 163 (accept_3_3 2 108 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 108 163 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 108 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  163)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 107 163 (Eq.refl Bool.true) (allA_of_3_1 57
  107 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 58 106 163 (Eq.refl Bool.true) (allA_succ_of_accept 57
  106 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 106 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 106 163 (accept_3_3 56 106 163 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 106 163 (Polychromatic418967fa.accept_7_6_1_2_1_230 55 106 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 106 163 (Polychromatic418967fa.accept_22_10_18_9_1_5685 54 106
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 106 163 (accept_3_3 53 106
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 106 163
  (Polychromatic418967fa.accept_7_3_1_2_1_247 52 106 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 106 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 106 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 106 163 (accept_3_3 50 106 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 106 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 106 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 106 163 (Polychromatic418967fa.accept_7_6_1_2_1_230
  48 106 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 106 163 (accept_3_3 47
  106 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 106 163
  (Polychromatic418967fa.accept_11_2_7_9_1_890 46 106 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 106 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 106 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 106 163 (accept_3_3 44 106 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 106 163 (Polychromatic418967fa.accept_14_1_8_9_1_1312 43 106 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 106 163
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 106 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 106 163 (accept_3_3 41 106 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 106 163 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 106 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 106 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 106 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 106 163 (accept_3_3 38 106 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 106 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 106 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 106 163
  (Polychromatic418967fa.accept_21_15_1_16_1_2930 36 106 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 106 163 (accept_3_3 35 106 163 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 106 163 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 106 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 106 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 106 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 106 163 (accept_3_3 32 106 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 106 163 (Polychromatic418967fa.accept_7_3_1_2_1_247
  31 106 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 106 163
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 106 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 106 163 (accept_3_3 29 106 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 106 163 (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 106 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 106 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 106 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 106 163 (accept_3_3 26 106 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 106 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 106 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 106 163
  (Polychromatic418967fa.accept_7_3_1_2_1_247 24 106 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 106 163 (accept_3_3 23 106 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 106 163 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 106 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 106 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 106 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 106 163 (accept_3_3 20 106 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 106 163 (Polychromatic418967fa.accept_10_9_6_3_1_545 19 106 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 106 163
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 106 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 106 163 (accept_3_3 17 106 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 106 163 (Polychromatic418967fa.accept_11_5_7_9_1_2696 16 106 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 106 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 106 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 106 163 (accept_3_3 14 106 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 106 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 106 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 106 163
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 106 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 106 163 (accept_3_3 11 106 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 106 163 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 106 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 106 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 106 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 106 163 (accept_3_3 8 106 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 106 163 (Polychromatic418967fa.accept_10_7_6_3_1_927 7 106 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 106 163
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 106 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 106 163 (accept_3_3 5 106 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  106 163 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 106 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 106 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 106 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 106 163 (accept_3_3 2 106 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 106 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 106 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106
  163)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 105 163 (Eq.refl Bool.true)
  (allA_succ_of_accept 58 105 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 105 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 105 163 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 105 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 105 163 (accept_3_3 56 105 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 105 163 (Polychromatic418967fa.accept_13_3_1_7_1_1706
  55 105 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 105 163
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 105 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 105 163 (accept_3_3 53 105 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 105 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 105 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 105 163 (Polychromatic418967fa.accept_12_3_9_7_1_472 51 105 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 105 163 (accept_3_3 50 105 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 105 163 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 105 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 105 163
  (Polychromatic418967fa.accept_9_3_6_1_1_24 48 105 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 105 163 (accept_3_3 47 105 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 105 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 105 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 105 163 (Polychromatic418967fa.accept_13_6_1_7_1_1690 45 105 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 105 163 (accept_3_3 44 105 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 163 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 105 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 105 163
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 105 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 105 163 (accept_3_3 41 105 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 105 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 105 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 105 163 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 105 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 105 163 (accept_3_3 38 105 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 163 (Polychromatic418967fa.accept_10_7_5_3_1_542 37 105 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 105 163
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 105 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 105 163 (accept_3_3 35 105 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 105 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 105 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 105 163 (Polychromatic418967fa.accept_14_5_7_9_1_3828 33 105 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 163 (accept_3_3 32 105 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 163 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 105 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 105 163
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 105 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 105 163 (accept_3_3 29 105 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 105 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 105 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 105 163 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 105 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 163 (accept_3_3 26 105 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 163 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 105 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 105 163
  (Polychromatic418967fa.accept_13_11_1_7_1_1691 24 105 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 105 163 (accept_3_3 23 105 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 105 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 105 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 105 163 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 105 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 105 163 (accept_3_3 20 105 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 163 (Polychromatic418967fa.accept_13_6_1_7_1_1690 19 105 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 163
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 105 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 105 163 (accept_3_3 17 105 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 105 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 105 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 105 163 (Polychromatic418967fa.accept_12_3_9_7_1_472 15 105 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 105 163 (accept_3_3 14 105 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 163 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 105 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 163
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 105 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 105 163 (accept_3_3 11 105 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 105 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 105 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 105 163 (Polychromatic418967fa.accept_17_9_3_10_1_9070 9 105 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 105 163 (accept_3_3 8 105 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 163 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 105 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 105 163
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 105 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 105 163 (accept_3_3 5 105 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  105 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 105 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 105 163 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 105 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 163 (accept_3_3 2 105 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 163 (Polychromatic418967fa.accept_19_1_10_11_1_4721 1 105 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  163))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 104 163 (Eq.refl Bool.true) (allA_of_3_1
  60 104 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 61 103 163 (Eq.refl Bool.true) (allA_succ_of_accept 60
  103 163 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 103 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 103 163 (accept_3_3 59 103 163 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 103 163 (Polychromatic418967fa.accept_13_6_12_7_1_5131 58 103 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 103 163 (Polychromatic418967fa.accept_9_3_4_1_1_22 57 103 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 103 163 (accept_3_3 56 103 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 103 163
  (Polychromatic418967fa.accept_19_17_8_11_1_7605 55 103 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 103 163 (Polychromatic418967fa.accept_19_16_8_11_1_6080 54 103 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 103 163 (accept_3_3 53 103 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 103 163 (Polychromatic418967fa.accept_7_3_5_2_1_17 52 103 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 103 163
  (Polychromatic418967fa.accept_9_6_4_1_1_390 51 103 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 103 163 (accept_3_3 50 103 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 103 163 (Polychromatic418967fa.accept_13_10_12_7_1_1079 49 103 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 103 163 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 103 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 103 163 (accept_3_3 47 103 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 103 163 (Polychromatic418967fa.accept_7_4_5_2_1_243 46 103 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 103 163
  (Polychromatic418967fa.accept_7_3_5_2_1_17 45 103 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 103 163 (accept_3_3 44 103 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 103 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 103 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 103 163 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 103 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 103 163 (accept_3_3 41 103 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 103 163 (Polychromatic418967fa.accept_19_2_8_11_1_7701 40 103 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 103 163
  (Polychromatic418967fa.accept_7_4_5_2_1_243 39 103 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 103 163 (accept_3_3 38 103 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 103 163 (Polychromatic418967fa.accept_13_11_12_7_1_2443 37 103 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 103 163 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 103 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 103 163 (accept_3_3 35 103 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 103 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 103 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 103 163
  (Polychromatic418967fa.accept_9_6_4_1_1_390 33 103 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 103 163 (accept_3_3 32 103 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 103 163 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 103 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 103 163 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 103 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 103 163 (accept_3_3 29 103 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 103 163 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 103 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 103 163
  (Polychromatic418967fa.accept_16_11_7_3_1_3163 27 103 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 103 163 (accept_3_3 26 103 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 103 163 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 103 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 103 163 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 103 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 103 163 (accept_3_3 23 103 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 103 163 (Polychromatic418967fa.accept_19_3_8_11_1_7609 22 103 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 103 163
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 103 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 103 163 (accept_3_3 20 103 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 103 163 (Polychromatic418967fa.accept_13_6_12_7_1_5131 19 103 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 103 163 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 103 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 103 163 (accept_3_3 17 103 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 103 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 103 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 103 163
  (Polychromatic418967fa.accept_9_6_4_1_1_390 15 103 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 103 163 (accept_3_3 14 103 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 103 163 (Polychromatic418967fa.accept_11_2_4_9_1_484 13 103 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 103 163 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 103 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 103 163 (accept_3_3 11 103 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 103 163 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 103 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 103 163
  (Polychromatic418967fa.accept_16_9_7_3_1_614 9 103 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 103 163 (accept_3_3 8 103 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  103 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 103 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 103 163 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 103 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 103 163 (accept_3_3 5 103 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 103 163 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 103 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 103 163
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 103 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 103 163 (accept_3_3 2 103 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  103 163 (Polychromatic418967fa.accept_19_1_8_11_1_3378 1 103 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 103 163))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 102 163
  (Eq.refl Bool.true) (allA_succ_of_accept 61 102 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 102 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 102 163
  (Polychromatic418967fa.accept_9_6_3_1_1_155 60 102 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 102 163 (accept_3_3 59 102 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 102 163 (Polychromatic418967fa.accept_9_4_3_1_1_154 58 102 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 102 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 102 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 102 163 (accept_3_3 56 102 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 102 163 (Polychromatic418967fa.accept_7_6_4_2_1_236 55 102 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 102 163
  (Polychromatic418967fa.accept_7_5_4_2_1_235 54 102 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 102 163 (accept_3_3 53 102 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 102 163 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 102 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 102 163 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 102 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 102 163 (accept_3_3 50 102 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 102 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 102 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 102 163
  (Polychromatic418967fa.accept_7_6_4_2_1_236 48 102 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 102 163 (accept_3_3 47 102 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 102 163 (Polychromatic418967fa.accept_15_1_12_13_1_944 46 102 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 102 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 102 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 102 163 (accept_3_3 44 102 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 102 163 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 102 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 102 163
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 102 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 102 163 (accept_3_3 41 102 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 102 163 (Polychromatic418967fa.accept_7_5_4_2_1_235 40 102 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 102 163 (Polychromatic418967fa.accept_11_6_3_9_1_906 39 102 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 102 163 (accept_3_3 38 102 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 102 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 102 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 102 163
  (Polychromatic418967fa.accept_16_4_6_3_1_1311 36 102 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 102 163 (accept_3_3 35 102 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 102 163 (Polychromatic418967fa.accept_7_6_4_2_1_236 34 102 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 102 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 102 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 102 163 (accept_3_3 32 102 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 102 163 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 102 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 102 163
  (Polychromatic418967fa.accept_13_4_11_7_1_558 30 102 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 102 163 (accept_3_3 29 102 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 102 163 (Polychromatic418967fa.accept_11_6_3_9_1_906 28 102 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 102 163 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 102 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 102 163 (accept_3_3 26 102 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 102 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 102 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 102 163
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 102 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 102 163 (accept_3_3 23 102 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 102 163 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 102 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 102 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 102 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 102 163 (accept_3_3 20 102 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 102 163 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 102 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 102 163
  (Polychromatic418967fa.accept_13_5_11_7_1_559 18 102 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 102 163 (accept_3_3 17 102 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 102 163 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 102 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 102 163 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 102 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 102 163 (accept_3_3 14 102 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 102 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 102 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 102 163
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 102 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 102 163 (accept_3_3 11 102 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 102 163 (Polychromatic418967fa.accept_15_10_12_13_1_2585 10 102 163 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 102 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 102 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 102 163 (accept_3_3 8 102 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 102 163 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 102 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 102 163
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 102 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 102 163 (accept_3_3 5 102 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  102 163 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 102 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 102 163 (Polychromatic418967fa.accept_13_3_11_7_1_2488 3 102 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 102 163 (accept_3_3 2 102 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 102 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 102 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  163)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 101 163 (Eq.refl Bool.true)
  (allA_of_3_1 63 101 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 64 100 163 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 100 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 100 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 100 163 (accept_3_3 62 100 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 100 163 (Polychromatic418967fa.accept_15_1_10_13_1_939 61 100 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 100 163
  (Polychromatic418967fa.accept_13_8_9_7_1_530 60 100 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 100 163 (accept_3_3 59 100 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 100 163 (Polychromatic418967fa.accept_12_10_4_7_1_948 58 100 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 100 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 100 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 100 163 (accept_3_3 56 100 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 100 163 (Polychromatic418967fa.accept_8_7_4_3_1_156 55 100 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 100 163
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 54 100 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 100 163 (accept_3_3 53 100 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 100 163 (Polychromatic418967fa.accept_18_16_10_1_1_3696 52 100 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 100 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 100 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 100 163 (accept_3_3 50 100 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 100 163 (Polychromatic418967fa.accept_14_7_2_9_1_2093 49 100 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 100 163
  (Polychromatic418967fa.accept_15_3_10_13_1_2605 48 100 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 100 163 (accept_3_3 47 100 163 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 100 163 (Polychromatic418967fa.accept_12_10_4_7_1_948 46 100 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 100 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 100 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 100 163 (accept_3_3 44 100 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 100 163
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 43 100 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 100 163 (Polychromatic418967fa.accept_13_3_9_7_1_1730 42 100 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 100 163 (accept_3_3 41 100 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 100 163 (Polychromatic418967fa.accept_16_8_4_3_1_3146 40 100 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 100 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 100 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 100 163 (accept_3_3 38 100 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 100 163 (Polychromatic418967fa.accept_13_11_9_7_1_2484 37 100 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 100 163 (Polychromatic418967fa.accept_17_2_15_10_1_5171 36 100 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 100 163 (accept_3_3 35 100 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 100 163 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 100
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 100 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 100 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 100 163 (accept_3_3 32 100 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 100 163 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 100 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 100 163 (Polychromatic418967fa.accept_13_4_9_7_1_2402 30 100 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 100 163 (accept_3_3 29 100 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 100 163 (Polychromatic418967fa.accept_13_2_9_7_1_164 28 100
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 100 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 100 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 100 163 (accept_3_3 26 100 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 100 163 (Polychromatic418967fa.accept_14_11_2_9_1_5873 25 100 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 100 163 (Polychromatic418967fa.accept_13_11_9_7_1_2484 24 100 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 100 163 (accept_3_3 23 100 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 100 163 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 100
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 100 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 100 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 100 163 (accept_3_3 20 100 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 100 163 (Polychromatic418967fa.accept_13_6_9_7_1_2430 19 100 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 100 163 (Polychromatic418967fa.accept_14_4_2_9_1_2092 18 100 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 100 163 (accept_3_3 17 100 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 100 163 (Polychromatic418967fa.accept_13_3_9_7_1_1730 16 100
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 100 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 100 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 100 163 (accept_3_3 14 100 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 100 163 (Polychromatic418967fa.accept_18_13_10_1_1_9025 13 100 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 100 163 (Polychromatic418967fa.accept_15_12_10_13_1_4497 12 100 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 100 163 (accept_3_3 11 100 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 100 163 (Polychromatic418967fa.accept_11_10_1_9_1_2060 10 100
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 100 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 100 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 100 163 (accept_3_3 8 100 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  100 163 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 100 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 100 163 (Polychromatic418967fa.accept_13_6_9_7_1_2430 6 100 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 100 163 (accept_3_3 5 100 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 100 163 (Polychromatic418967fa.accept_13_4_9_7_1_2402 4 100 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 100 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 100 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 100 163 (accept_3_3 2 100 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  100 163 (Polychromatic418967fa.accept_15_1_10_13_1_939 1 100 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 100 163)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 99 163
  (Eq.refl Bool.true) (allA_succ_of_accept 64 99 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 99 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 163
  (Polychromatic418967fa.accept_15_3_9_13_1_1681 63 99 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 99 163 (accept_3_3 62 99 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  99 163 (Polychromatic418967fa.accept_13_9_8_7_1_1073 61 99 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 99 163 (Polychromatic418967fa.accept_18_6_9_1_1_3769 60 99 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 99 163 (accept_3_3 59 99 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 99 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 163
  (Polychromatic418967fa.accept_12_9_3_7_1_924 57 99 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 99 163 (accept_3_3 56 99 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  99 163 (Polychromatic418967fa.accept_7_6_1_2_1_230 55 99 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 99 163 (Polychromatic418967fa.accept_10_4_9_3_1_1907 54 99 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 99 163 (accept_3_3 53 99 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 99 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 163
  (Polychromatic418967fa.accept_13_12_8_7_1_2526 51 99 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 99 163 (accept_3_3 50 99 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  99 163 (Polychromatic418967fa.accept_13_10_8_7_1_1074 49 99 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 99 163 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 99 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 99 163 (accept_3_3 47 99 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 99 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 163
  (Polychromatic418967fa.accept_7_3_1_2_1_247 45 99 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 99 163 (accept_3_3 44 99 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  99 163 (Polychromatic418967fa.accept_21_1_15_16_1_5891 43 99 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 99 163 (Polychromatic418967fa.accept_13_3_8_7_1_4135 42 99 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 99 163 (accept_3_3 41 99 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 99 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 163
  (Polychromatic418967fa.accept_17_5_14_10_1_2831 39 99 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 99 163 (accept_3_3 38 99 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  99 163 (Polychromatic418967fa.accept_15_7_9_13_1_3451 37 99 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 99 163 (Polychromatic418967fa.accept_10_6_9_3_1_935 36 99 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 99 163 (accept_3_3 35 99 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 99 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 163
  (Polychromatic418967fa.accept_12_9_3_7_1_924 33 99 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 99 163 (accept_3_3 32 99 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  99 163 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 99 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 99 163 (Polychromatic418967fa.accept_17_13_14_10_1_1847 30 99 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 163 (accept_3_3 29 99 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 99 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 163
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 99 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 99 163 (accept_3_3 26 99 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  99 163 (Polychromatic418967fa.accept_13_12_8_7_1_2526 25 99 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 99 163 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 99 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 99 163 (accept_3_3 23 99 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 99 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 163
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 99 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 99 163 (accept_3_3 20 99 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  99 163 (Polychromatic418967fa.accept_15_4_9_13_1_2582 19 99 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 99 163 (Polychromatic418967fa.accept_15_3_9_13_1_1681 18 99 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 163 (accept_3_3 17 99 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 99 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 163
  (Polychromatic418967fa.accept_13_2_8_7_1_2424 15 99 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 99 163 (accept_3_3 14 99 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  99 163 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 99 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 99 163 (Polychromatic418967fa.accept_13_12_8_7_1_2526 12 99 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 99 163 (accept_3_3 11 99 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 99 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 163
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 99 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 99 163 (accept_3_3 8 99 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99
  163 (Polychromatic418967fa.accept_15_7_9_13_1_3451 7 99 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 99 163 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 99 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 163 (accept_3_3 5 99 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 99 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99 163
  (Polychromatic418967fa.accept_7_3_1_2_1_247 3 99 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 99 163 (accept_3_3 2 99 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99
  163 (Polychromatic418967fa.accept_13_1_8_7_1_1088 1 99 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 99 163))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 98 163
  (Eq.refl Bool.true) (allA_of_3_1 66 98 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 67 97 163 (Eq.refl
  Bool.true) (allA_succ_of_accept 66 97 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 97 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 97 163 (accept_3_3 65 97 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 97 163 (Polychromatic418967fa.accept_7_1_6_2_1_18 64 97 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 97 163
  (Polychromatic418967fa.accept_26_11_19_7_1_9069 63 97 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 97 163 (accept_3_3 62 97 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  97 163 (Polychromatic418967fa.accept_13_9_6_7_1_551 61 97 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 97 163 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 97 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 97 163 (accept_3_3 59 97 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 97 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 97 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 97 163
  (Polychromatic418967fa.accept_7_1_6_2_1_18 57 97 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 97 163 (accept_3_3 56 97 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  97 163 (Polychromatic418967fa.accept_10_5_7_3_1_561 55 97 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 97 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 97 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 97 163 (accept_3_3 53 97 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 97 163 (Polychromatic418967fa.accept_7_3_6_2_1_90 52 97 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 97 163
  (Polychromatic418967fa.accept_9_6_7_1_1_145 51 97 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 97 163 (accept_3_3 50 97 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  97 163 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 97 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 97 163 (Polychromatic418967fa.accept_9_3_7_1_1_143 48 97 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 97 163 (accept_3_3 47 97 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 97 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 97 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 97 163
  (Polychromatic418967fa.accept_7_3_6_2_1_90 45 97 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 97 163 (accept_3_3 44 97 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  97 163 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 97 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 97 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 97 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 97 163 (accept_3_3 41 97 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 97 163 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 97 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 97 163
  (Polychromatic418967fa.accept_7_4_6_2_1_451 39 97 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 97 163 (accept_3_3 38 97 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  97 163 (Polychromatic418967fa.accept_24_13_1_19_1_7174 37 97 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 97 163 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 97 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 97 163 (accept_3_3 35 97 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 97 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 97 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 97 163
  (Polychromatic418967fa.accept_9_6_7_1_1_145 33 97 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 97 163 (accept_3_3 32 97 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  97 163 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 97 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 97 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 97 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 97 163 (accept_3_3 29 97 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 97 163 (Polychromatic418967fa.accept_19_9_2_11_1_7581 28 97 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 97 163
  (Polychromatic418967fa.accept_13_1_6_7_1_550 27 97 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 97 163 (accept_3_3 26 97 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  97 163 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 97 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 97 163 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 97 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 97 163 (accept_3_3 23 97 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 97 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 97 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 97 163
  (Polychromatic418967fa.accept_9_3_7_1_1_143 21 97 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 97 163 (accept_3_3 20 97 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  97 163 (Polychromatic418967fa.accept_17_2_12_10_1_9034 19 97 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 97 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 97 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 97 163 (accept_3_3 17 97 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 97 163 (Polychromatic418967fa.accept_10_6_7_3_1_547 16 97 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 97 163
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 97 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 97 163 (accept_3_3 14 97 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  97 163 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 97 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 97 163 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 97 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 97 163 (accept_3_3 11 97 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 97 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 97 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 97 163
  (Polychromatic418967fa.accept_13_9_6_7_1_551 9 97 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 97 163 (accept_3_3 8 97 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 97
  163 (Polychromatic418967fa.accept_21_7_13_16_1_9068 7 97 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 97 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 97 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 97 163 (accept_3_3 5 97 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 97 163 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 97 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 97 163
  (Polychromatic418967fa.accept_7_3_6_2_1_90 3 97 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 97 163 (accept_3_3 2 97 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 97
  163 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 97 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 97 163))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 96 163 (Eq.refl
  Bool.true) (allA_succ_of_accept 67 96 163 (Polychromatic418967fa.accept_7_4_5_2_1_243 67 96 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 96 163 (Polychromatic418967fa.accept_7_3_5_2_1_17 66
  96 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 96 163 (accept_3_3 65 96
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 96 163
  (Polychromatic418967fa.accept_13_12_5_7_1_1696 64 96 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 96 163 (Polychromatic418967fa.accept_13_11_5_7_1_2420 63 96 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 96 163 (accept_3_3 62 96 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 96 163 (Polychromatic418967fa.accept_9_7_6_1_1_709 61 96 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 96 163 (Polychromatic418967fa.accept_7_4_5_2_1_243 60
  96 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 96 163 (accept_3_3 59 96
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 96 163
  (Polychromatic418967fa.accept_9_4_6_1_1_393 58 96 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 96 163 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 96 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 96 163 (accept_3_3 56 96 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 96 163 (Polychromatic418967fa.accept_17_4_11_10_1_5167 55 96 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 96 163
  (Polychromatic418967fa.accept_11_10_8_9_1_492 54 96 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 96 163 (accept_3_3 53 96 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  96 163 (Polychromatic418967fa.accept_7_3_5_2_1_17 52 96 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 96 163 (Polychromatic418967fa.accept_13_12_5_7_1_1696 51 96 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 96 163 (accept_3_3 50 96 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 96 163 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 96 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 96 163
  (Polychromatic418967fa.accept_9_3_6_1_1_24 48 96 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 96 163 (accept_3_3 47 96 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  96 163 (Polychromatic418967fa.accept_7_4_5_2_1_243 46 96 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 96 163 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 96 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 96 163 (accept_3_3 44 96 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 96 163 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 96 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 96 163
  (Polychromatic418967fa.accept_25_17_21_13_1_9067 42 96 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 96 163 (accept_3_3 41 96 163 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 96 163 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 96 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 96 163 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 96 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 96 163 (accept_3_3 38 96 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 96 163 (Polychromatic418967fa.accept_10_7_6_3_1_927
  37 96 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 96 163
  (Polychromatic418967fa.accept_23_13_4_2_1_9066 36 96 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 96 163 (accept_3_3 35 96 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  96 163 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 96 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 96 163 (Polychromatic418967fa.accept_20_13_16_3_1_4479 33 96 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 96 163 (accept_3_3 32 96 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 96 163 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 96 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 96 163
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 96 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 96 163 (accept_3_3 29 96 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  96 163 (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 96 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 96 163 (Polychromatic418967fa.accept_10_7_6_3_1_927 27 96 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 96 163 (accept_3_3 26 96 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 96 163 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 96 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 96 163
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 96 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 96 163 (accept_3_3 23 96 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  96 163 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 96 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 96 163 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 96 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 96 163 (accept_3_3 20 96 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 163 (Polychromatic418967fa.accept_10_9_6_3_1_545 19 96 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 96 163
  (Polychromatic418967fa.accept_7_4_5_2_1_243 18 96 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 96 163 (accept_3_3 17 96 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  96 163 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 96 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 96 163 (Polychromatic418967fa.accept_13_2_5_7_1_1695 15 96 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 96 163 (accept_3_3 14 96 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 163 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 96 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 96 163
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 96 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 96 163 (accept_3_3 11 96 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  96 163 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 96 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 96 163 (Polychromatic418967fa.accept_10_9_6_3_1_545 9 96 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 96 163 (accept_3_3 8 96 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 163 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 96 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 96 163
  (Polychromatic418967fa.accept_19_6_1_11_1_7579 6 96 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 96 163 (accept_3_3 5 96 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 96
  163 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 96 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 96 163 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 96 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 96 163 (accept_3_3 2 96 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 96 163 (Polychromatic418967fa.accept_17_1_11_10_1_5149 1 96 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  163)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 95 163 (Eq.refl Bool.true)
  (allA_of_3_1 69 95 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 70 94 163 (Eq.refl Bool.true)
  (allA_succ_of_accept 69 94 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 94 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 94 163 (accept_3_3 68 94 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 94 163 (Polychromatic418967fa.accept_10_7_4_3_1_560 67 94 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 94 163 (Polychromatic418967fa.accept_9_3_4_1_1_22 66
  94 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 94 163 (accept_3_3 65 94
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 94 163 (Polychromatic418967fa.accept_7_1_3_2_1_13
  64 94 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 94 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 94 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 94 163 (accept_3_3 62 94 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  94 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 94 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 94 163 (Polychromatic418967fa.accept_9_6_4_1_1_390 60 94 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 94 163 (accept_3_3 59 94 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 94 163 (Polychromatic418967fa.accept_11_3_6_9_1_1378 58 94 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 94 163
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 94 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 94 163 (accept_3_3 56 94 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  94 163 (Polychromatic418967fa.accept_7_6_3_2_1_461 55 94 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 94 163 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 94 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 94 163 (accept_3_3 53 94 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 94 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 94 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 94 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 94 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 94 163 (accept_3_3 50 94 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  94 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 94 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 94 163 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 94 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 94 163 (accept_3_3 47 94 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 94 163 (Polychromatic418967fa.accept_19_8_18_11_1_3408 46 94 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 94 163
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 94 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 94 163 (accept_3_3 44 94 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  94 163 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 94 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 94 163 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 94 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 94 163 (accept_3_3 41 94 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 94 163 (Polychromatic418967fa.accept_7_5_3_2_1_249 40 94 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 94 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 94 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 94 163 (accept_3_3 38 94 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  94 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 94 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 94 163 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 94 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 94 163 (accept_3_3 35 94 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 94 163 (Polychromatic418967fa.accept_7_6_3_2_1_461 34 94 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 94 163
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 94 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 94 163 (accept_3_3 32 94 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  94 163 (Polychromatic418967fa.accept_19_12_18_11_1_9065 31 94 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 94 163 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 94 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 94 163 (accept_3_3 29 94 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 94 163 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 94 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 94 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 94 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 94 163 (accept_3_3 26 94 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  94 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 94 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 94 163 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 94 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 94 163 (accept_3_3 23 94 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 94 163 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 94 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 94 163
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 94 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 94 163 (accept_3_3 20 94 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  94 163 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 94 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 94 163 (Polychromatic418967fa.accept_17_1_9_10_1_1864 18 94 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 94 163 (accept_3_3 17 94 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 94 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 94 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 94 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 94 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 94 163 (accept_3_3 14 94 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  94 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 94 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 94 163 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 94 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 94 163 (accept_3_3 11 94 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 94 163 (Polychromatic418967fa.accept_13_10_3_7_1_2517 10 94 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 94 163
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 94 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 94 163 (accept_3_3 8 94 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 94
  163 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 94 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 94 163 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 94 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 94 163 (accept_3_3 5 94 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 94 163 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 94 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 94 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 94
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 94 163 (accept_3_3 2 94 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 94 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 94
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94
  163)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 93 163 (Eq.refl Bool.true)
  (allA_succ_of_accept 70 93 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 93 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 93 163 (Polychromatic418967fa.accept_9_6_3_1_1_155 69 93 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 93 163 (accept_3_3 68 93 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 93 163 (Polychromatic418967fa.accept_9_4_3_1_1_154 67
  93 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 93 163
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 93 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 93 163 (accept_3_3 65 93 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  93 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 93 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 93 163 (Polychromatic418967fa.accept_12_3_9_7_1_472 63 93 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 93 163 (accept_3_3 62 93 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 93 163 (Polychromatic418967fa.accept_9_7_3_1_1_386 61 93 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 93 163
  (Polychromatic418967fa.accept_9_6_3_1_1_155 60 93 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 93 163 (accept_3_3 59 93 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  93 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 93 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 93 163 (Polychromatic418967fa.accept_13_5_2_7_1_2414 57 93 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 93 163 (accept_3_3 56 93 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 93 163 (Polychromatic418967fa.accept_15_10_3_13_1_4480 55 93 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 93 163
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 93 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 93 163 (accept_3_3 53 93 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  93 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 93 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 93 163 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 93 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 93 163 (accept_3_3 50 93 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 93 163 (Polychromatic418967fa.accept_9_4_3_1_1_154 49 93 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 93 163
  (Polychromatic418967fa.accept_13_9_2_7_1_1083 48 93 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 93 163 (accept_3_3 47 93 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  93 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 93 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 93 163 (Polychromatic418967fa.accept_18_9_3_1_1_2559 45 93 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 93 163 (accept_3_3 44 93 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 93 163 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 93 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 93 163
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 93 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 93 163 (accept_3_3 41 93 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  93 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 93 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 93 163 (Polychromatic418967fa.accept_12_3_9_7_1_472 39 93 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 93 163 (accept_3_3 38 93 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 93 163 (Polychromatic418967fa.accept_19_18_17_11_1_9064 37 93 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 93 163
  (Polychromatic418967fa.accept_17_2_8_10_1_2870 36 93 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 93 163 (accept_3_3 35 93 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  93 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 93 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 93 163 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 93 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 93 163 (accept_3_3 32 93 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 93 163 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 93 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 93 163
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 93 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 93 163 (accept_3_3 29 93 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  93 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 93 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 93 163 (Polychromatic418967fa.accept_12_3_9_7_1_472 27 93 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 163 (accept_3_3 26 93 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 93 163 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 93 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 93 163
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 93 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 93 163 (accept_3_3 23 93 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  93 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 93 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 93 163 (Polychromatic418967fa.accept_13_8_2_7_1_2452 21 93 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 163 (accept_3_3 20 93 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 163 (Polychromatic418967fa.accept_17_2_8_10_1_2870 19 93 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 93 163
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 93 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 93 163 (accept_3_3 17 93 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  93 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 93 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 93 163 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 93 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 163 (accept_3_3 14 93 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 163 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 93 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 93 163
  (Polychromatic418967fa.accept_15_12_3_13_1_4481 12 93 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 93 163 (accept_3_3 11 93 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  93 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 93 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 93 163 (Polychromatic418967fa.accept_13_9_2_7_1_1083 9 93 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 163 (accept_3_3 8 93 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 163 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 93 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93 163
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 93 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 163 (accept_3_3 5 93 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93
  163 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 93 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 93 163 (Polychromatic418967fa.accept_12_3_9_7_1_472 3 93 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 163 (accept_3_3 2 93 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 93 163 (Polychromatic418967fa.accept_15_1_3_13_1_2548 1 93 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  163))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 92 163 (Eq.refl Bool.true)
  (allA_of_3_1 72 92 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 73 91 163 (Eq.refl Bool.true)
  (allA_succ_of_accept 72 91 163 (Polychromatic418967fa.accept_10_2_1_3_1_233 72 91 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 91 163 (accept_3_3 71 91 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 91 163 (Polychromatic418967fa.accept_15_10_1_13_1_2609 70 91 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 91 163
  (Polychromatic418967fa.accept_21_6_7_16_1_9035 69 91 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 91 163 (accept_3_3 68 91 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  91 163 (Polychromatic418967fa.accept_17_16_6_10_1_1863 67 91 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 91 163 (Polychromatic418967fa.accept_19_9_15_11_1_7687 66 91 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 91 163 (accept_3_3 65 91 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 91 163 (Polychromatic418967fa.accept_19_7_15_11_1_3420 64 91
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 91 163
  (Polychromatic418967fa.accept_15_3_1_13_1_1672 63 91 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 91 163 (accept_3_3 62 91 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  91 163 (Polychromatic418967fa.accept_11_6_3_9_1_906 61 91 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 91 163 (Polychromatic418967fa.accept_22_16_3_9_1_9063 60 91 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 91 163 (accept_3_3 59 91 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 91 163 (Polychromatic418967fa.accept_10_8_1_3_1_1374 58 91 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 91 163
  (Polychromatic418967fa.accept_15_12_1_13_1_3444 57 91 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 91 163 (accept_3_3 56 91 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  91 163 (Polychromatic418967fa.accept_15_10_1_13_1_2609 55 91 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 91 163 (Polychromatic418967fa.accept_14_12_7_9_1_726 54 91 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 91 163 (accept_3_3 53 91 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 91 163 (Polychromatic418967fa.accept_10_2_1_3_1_233 52 91 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 91 163
  (Polychromatic418967fa.accept_21_9_7_16_1_5904 51 91 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 91 163 (accept_3_3 50 91 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  91 163 (Polychromatic418967fa.accept_22_5_3_9_1_9062 49 91 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 91 163 (Polychromatic418967fa.accept_10_8_1_3_1_1374 48 91 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 91 163 (accept_3_3 47 91 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 91 163 (Polychromatic418967fa.accept_16_14_11_3_1_4249 46 91 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 91 163
  (Polychromatic418967fa.accept_19_7_15_11_1_3420 45 91 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 91 163 (accept_3_3 44 91 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  91 163 (Polychromatic418967fa.accept_19_5_15_11_1_7568 43 91 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 91 163 (Polychromatic418967fa.accept_10_2_1_3_1_233 42 91 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 91 163 (accept_3_3 41 91 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 91 163 (Polychromatic418967fa.accept_14_12_7_9_1_726 40 91 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 91 163
  (Polychromatic418967fa.accept_11_6_3_9_1_906 39 91 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 91 163 (accept_3_3 38 91 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  91 163 (Polychromatic418967fa.accept_22_15_3_9_1_9061 37 91 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 91 163 (Polychromatic418967fa.accept_25_11_16_13_1_2000 36 91 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 91 163 (accept_3_3 35 91 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 91 163 (Polychromatic418967fa.accept_20_14_11_3_1_9060 34 91
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 91 163
  (Polychromatic418967fa.accept_14_5_7_9_1_3828 33 91 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 91 163 (accept_3_3 32 91 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  91 163 (Polychromatic418967fa.accept_16_15_11_3_1_2179 31 91 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 91 163 (Polychromatic418967fa.accept_14_2_7_9_1_2937 30 91 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 91 163 (accept_3_3 29 91 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 91 163 (Polychromatic418967fa.accept_10_8_1_3_1_1374 28 91 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 91 163
  (Polychromatic418967fa.accept_15_12_1_13_1_3444 27 91 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 91 163 (accept_3_3 26 91 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  91 163 (Polychromatic418967fa.accept_15_10_1_13_1_2609 25 91 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 91 163 (Polychromatic418967fa.accept_16_8_11_3_1_4279 24 91 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 91 163 (accept_3_3 23 91 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 91 163 (Polychromatic418967fa.accept_10_2_1_3_1_233 22 91 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 91 163
  (Polychromatic418967fa.accept_17_4_6_10_1_5164 21 91 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 91 163 (accept_3_3 20 91 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  91 163 (Polychromatic418967fa.accept_14_5_7_9_1_3828 19 91 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 91 163 (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 91 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 91 163 (accept_3_3 17 91 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 91 163 (Polychromatic418967fa.accept_14_2_7_9_1_2937 16 91 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 91 163
  (Polychromatic418967fa.accept_16_15_11_3_1_2179 15 91 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 91 163 (accept_3_3 14 91 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  91 163 (Polychromatic418967fa.accept_20_13_11_3_1_4509 13 91 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 91 163 (Polychromatic418967fa.accept_10_2_1_3_1_233 12 91 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 91 163 (accept_3_3 11 91 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 91 163 (Polychromatic418967fa.accept_15_10_1_13_1_2609 10 91 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 163
  (Polychromatic418967fa.accept_19_9_15_11_1_7687 9 91 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 91 163 (accept_3_3 8 91 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 91
  163 (Polychromatic418967fa.accept_16_7_11_3_1_1330 7 91 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 91 163 (Polychromatic418967fa.accept_11_6_3_9_1_906 6 91 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 91 163 (accept_3_3 5 91 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 91 163 (Polychromatic418967fa.accept_17_4_6_10_1_5164 4 91 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 91 163
  (Polychromatic418967fa.accept_15_3_1_13_1_1672 3 91 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 91 163 (accept_3_3 2 91 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 91
  163 (Polychromatic418967fa.accept_19_1_15_11_1_4712 1 91 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 91 163))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74
  90 163 (Eq.refl Bool.true) (allA_succ_of_accept 73 90 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 90 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 90 163
  (Polychromatic418967fa.accept_19_15_14_11_1_7682 72 90 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 90 163 (accept_3_3 71 90 163 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 90 163 (Polychromatic418967fa.accept_11_4_2_9_1_496 70 90 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 90 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 90 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 90 163 (accept_3_3 68 90 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 90 163 (Polychromatic418967fa.accept_7_4_6_2_1_451 67
  90 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 90 163
  (Polychromatic418967fa.accept_7_3_6_2_1_90 66 90 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 90 163 (accept_3_3 65 90 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  90 163 (Polychromatic418967fa.accept_7_1_6_2_1_18 64 90 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 90 163 (Polychromatic418967fa.accept_13_11_12_7_1_2443 63 90 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 90 163 (accept_3_3 62 90 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 90 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 90 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 90 163
  (Polychromatic418967fa.accept_7_4_6_2_1_451 60 90 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 90 163 (accept_3_3 59 90 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  90 163 (Polychromatic418967fa.accept_13_6_12_7_1_5131 58 90 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 90 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 90 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 90 163 (accept_3_3 56 90 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 90 163 (Polychromatic418967fa.accept_16_7_10_3_1_2210 55 90 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 90 163
  (Polychromatic418967fa.accept_19_16_14_11_1_4711 54 90 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 90 163 (accept_3_3 53 90 163 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 90 163 (Polychromatic418967fa.accept_7_3_6_2_1_90 52 90 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 90 163 (Polychromatic418967fa.accept_11_7_2_9_1_480 51 90 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 90 163 (accept_3_3 50 90 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 90 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 49
  90 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 90 163
  (Polychromatic418967fa.accept_11_4_2_9_1_496 48 90 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 90 163 (accept_3_3 47 90 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  90 163 (Polychromatic418967fa.accept_7_4_6_2_1_451 46 90 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 90 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 90 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 90 163 (accept_3_3 44 90 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 90 163 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 90 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 90 163
  (Polychromatic418967fa.accept_20_2_10_3_1_9059 42 90 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 90 163 (accept_3_3 41 90 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  90 163 (Polychromatic418967fa.accept_11_7_2_9_1_480 40 90 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 90 163 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 90 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 90 163 (accept_3_3 38 90 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 90 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 90 163
  (Polychromatic418967fa.accept_7_1_6_2_1_18 36 90 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 90 163 (accept_3_3 35 90 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  90 163 (Polychromatic418967fa.accept_13_8_12_7_1_2442 34 90 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 90 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 90 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 90 163 (accept_3_3 32 90 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 90 163 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 90 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 90 163
  (Polychromatic418967fa.accept_13_4_12_7_1_2439 30 90 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 90 163 (accept_3_3 29 90 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  90 163 (Polychromatic418967fa.accept_16_12_10_3_1_4209 28 90 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 90 163 (Polychromatic418967fa.accept_20_7_10_3_1_949 27 90 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 90 163 (accept_3_3 26 90 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 90 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 90 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 90 163
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 90 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 90 163 (accept_3_3 23 90 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  90 163 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 90 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 90 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 90 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 90 163 (accept_3_3 20 90 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 90 163 (Polychromatic418967fa.accept_13_6_12_7_1_5131 19 90 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 90 163
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 90 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 90 163 (accept_3_3 17 90 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  90 163 (Polychromatic418967fa.accept_19_16_14_11_1_4711 16 90 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 90 163 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 90 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 90 163 (accept_3_3 14 90 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 90 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 90 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 90 163
  (Polychromatic418967fa.accept_16_12_10_3_1_4209 12 90 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 90 163 (accept_3_3 11 90 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  90 163 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 90 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 90 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 90 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 90 163 (accept_3_3 8 90 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 163 (Polychromatic418967fa.accept_11_7_2_9_1_480 7 90 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 90 163
  (Polychromatic418967fa.accept_13_6_12_7_1_5131 6 90 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 90 163 (accept_3_3 5 90 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 90
  163 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 90 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 90 163 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 90 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 90 163 (accept_3_3 2 90 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 90 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 90 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  163)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 89 163 (Eq.refl
  Bool.true) (allA_of_3_1 75 89 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 76 88 163 (Eq.refl Bool.true)
  (allA_succ_of_accept 75 88 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 88 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 88 163 (accept_3_3 74 88 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 88 163 (Polychromatic418967fa.accept_13_8_10_7_1_1702 73 88 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 88 163
  (Polychromatic418967fa.accept_14_2_4_9_1_2121 72 88 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 88 163 (accept_3_3 71 88 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  88 163 (Polychromatic418967fa.accept_12_10_4_7_1_948 70 88 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 88 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 88 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 88 163 (accept_3_3 68 88 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 88 163 (Polychromatic418967fa.accept_9_4_7_1_1_379 67 88 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 88 163
  (Polychromatic418967fa.accept_9_3_7_1_1_143 66 88 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 88 163 (accept_3_3 65 88 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  88 163 (Polychromatic418967fa.accept_13_12_10_7_1_2433 64 88 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 88 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 88 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 88 163 (accept_3_3 62 88 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 88 163 (Polychromatic418967fa.accept_7_5_4_2_1_235 61 88 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 88 163
  (Polychromatic418967fa.accept_9_6_7_1_1_145 60 88 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 88 163 (accept_3_3 59 88 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  88 163 (Polychromatic418967fa.accept_9_4_7_1_1_379 58 88 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 88 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 88 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 88 163 (accept_3_3 56 88 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 88 163 (Polychromatic418967fa.accept_7_6_4_2_1_236 55 88 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 88 163
  (Polychromatic418967fa.accept_7_5_4_2_1_235 54 88 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 88 163 (accept_3_3 53 88 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  88 163 (Polychromatic418967fa.accept_16_4_8_3_1_4206 52 88 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 88 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 88 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 88 163 (accept_3_3 50 88 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 88 163 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 88 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 88 163
  (Polychromatic418967fa.accept_7_6_4_2_1_236 48 88 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 88 163 (accept_3_3 47 88 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  88 163 (Polychromatic418967fa.accept_10_6_8_3_1_930 46 88 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 88 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 88 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 88 163 (accept_3_3 44 88 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 88 163 (Polychromatic418967fa.accept_13_4_10_7_1_1701 43 88 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 88 163
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 88 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 88 163 (accept_3_3 41 88 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  88 163 (Polychromatic418967fa.accept_7_5_4_2_1_235 40 88 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 88 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 88 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 88 163 (accept_3_3 38 88 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 88 163 (Polychromatic418967fa.accept_16_5_8_3_1_4240 37 88 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 88 163
  (Polychromatic418967fa.accept_10_6_8_3_1_930 36 88 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 88 163 (accept_3_3 35 88 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  88 163 (Polychromatic418967fa.accept_7_6_4_2_1_236 34 88 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 88 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 88 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 88 163 (accept_3_3 32 88 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 88 163 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 88 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 88 163
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 88 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 88 163 (accept_3_3 29 88 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  88 163 (Polychromatic418967fa.accept_16_12_8_3_1_4241 28 88 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 88 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 88 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 88 163 (accept_3_3 26 88 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 88 163 (Polychromatic418967fa.accept_10_5_8_3_1_229 25 88 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 88 163
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 88 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 88 163 (accept_3_3 23 88 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  88 163 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 88 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 88 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 88 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 88 163 (accept_3_3 20 88 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 88 163 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 88 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 88 163
  (Polychromatic418967fa.accept_19_18_12_11_1_3386 18 88 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 88 163 (accept_3_3 17 88 163 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 88 163 (Polychromatic418967fa.accept_10_6_8_3_1_930 16 88 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 88 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 88 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 88 163 (accept_3_3 14 88 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 88 163 (Polychromatic418967fa.accept_7_6_4_2_1_236 13
  88 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 88 163
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 88 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 88 163 (accept_3_3 11 88 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  88 163 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 88 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 88 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 88 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 88 163 (accept_3_3 8 88 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 88 163 (Polychromatic418967fa.accept_17_7_3_10_1_2881 7 88 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 88 163
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 88 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 88 163 (accept_3_3 5 88 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 88
  163 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 88 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 88 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 88 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 88 163 (accept_3_3 2 88 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 88 163 (Polychromatic418967fa.accept_10_1_8_3_1_947 1 88 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88
  163)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 87 163 (Eq.refl
  Bool.true) (allA_succ_of_accept 76 87 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 87 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 163 (Polychromatic418967fa.accept_7_5_3_2_1_249 75
  87 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 87 163 (accept_3_3 74 87
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 87 163
  (Polychromatic418967fa.accept_13_8_9_7_1_530 73 87 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 87 163 (Polychromatic418967fa.accept_21_9_3_16_1_1684 72 87 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 87 163 (accept_3_3 71 87 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 87 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 87 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 163 (Polychromatic418967fa.accept_7_6_3_2_1_461 69
  87 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 87 163 (accept_3_3 68 87
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 87 163
  (Polychromatic418967fa.accept_9_4_6_1_1_393 67 87 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 87 163 (Polychromatic418967fa.accept_9_3_6_1_1_24 66 87 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 87 163 (accept_3_3 65 87 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 87 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 87 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 163 (Polychromatic418967fa.accept_11_8_10_9_1_1401
  63 87 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 87 163 (accept_3_3 62
  87 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 87 163
  (Polychromatic418967fa.accept_7_5_3_2_1_249 61 87 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 87 163 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 87 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 87 163 (accept_3_3 59 87 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 87 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 87 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 163 (Polychromatic418967fa.accept_7_1_3_2_1_13 57
  87 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 87 163 (accept_3_3 56 87
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 87 163
  (Polychromatic418967fa.accept_7_6_3_2_1_461 55 87 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 87 163 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 87 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 87 163 (accept_3_3 53 87 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 87 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 87 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 163 (Polychromatic418967fa.accept_21_9_3_16_1_1684
  51 87 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 87 163 (accept_3_3 50
  87 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 163
  (Polychromatic418967fa.accept_9_4_6_1_1_393 49 87 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 87 163 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 87 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 87 163 (accept_3_3 47 87 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 87 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 87 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 163 (Polychromatic418967fa.accept_10_5_7_3_1_561
  45 87 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 87 163 (accept_3_3 44
  87 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 87 163
  (Polychromatic418967fa.accept_7_1_3_2_1_13 43 87 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 87 163 (Polychromatic418967fa.accept_13_3_9_7_1_1730 42 87 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 87 163 (accept_3_3 41 87 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 87 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 87 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 163 (Polychromatic418967fa.accept_9_3_6_1_1_24 39
  87 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 87 163 (accept_3_3 38 87
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 87 163
  (Polychromatic418967fa.accept_13_11_9_7_1_2484 37 87 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 87 163 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 87 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 87 163 (accept_3_3 35 87 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 87 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 87 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 163 (Polychromatic418967fa.accept_7_5_3_2_1_249 33
  87 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 87 163 (accept_3_3 32 87
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 163
  (Polychromatic418967fa.accept_9_4_6_1_1_393 31 87 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 87 163 (Polychromatic418967fa.accept_9_3_6_1_1_24 30 87 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 163 (accept_3_3 29 87 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 87 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 87 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 163 (Polychromatic418967fa.accept_7_6_3_2_1_461 27
  87 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 87 163 (accept_3_3 26 87
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 163
  (Polychromatic418967fa.accept_9_7_6_1_1_709 25 87 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 87 163 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 87 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 163 (accept_3_3 23 87 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 87 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 87 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 163 (Polychromatic418967fa.accept_9_3_6_1_1_24 21
  87 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 87 163 (accept_3_3 20 87
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 163
  (Polychromatic418967fa.accept_7_5_3_2_1_249 19 87 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 87 163 (Polychromatic418967fa.accept_15_3_12_13_1_2549 18 87 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 163 (accept_3_3 17 87 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 87 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 87 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 163 (Polychromatic418967fa.accept_7_1_3_2_1_13 15
  87 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 163 (accept_3_3 14 87
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 163
  (Polychromatic418967fa.accept_7_6_3_2_1_461 13 87 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 87 163 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 87 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 163 (accept_3_3 11 87 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 87 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 87 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 163 (Polychromatic418967fa.accept_12_9_3_7_1_924 9
  87 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 163 (accept_3_3 8 87 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 163 (Polychromatic418967fa.accept_9_7_6_1_1_709 7
  87 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87 163
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 87 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 87 163 (accept_3_3 5 87 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87
  163 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 87 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 87 163 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 87 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 163 (accept_3_3 2 87 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 87 163 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 87 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  163))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 78 86 163 (Eq.refl
  Bool.true) (allA_of_3_1 78 86 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 79 85 163 (Eq.refl Bool.true)
  (allA_succ_of_accept 78 85 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 85 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 85 163 (accept_3_3 77 85 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 85 163 (Polychromatic418967fa.accept_7_6_1_2_1_230 76 85 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 85 163 (Polychromatic418967fa.accept_9_3_4_1_1_22 75
  85 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 85 163 (accept_3_3 74 85
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 85 163
  (Polychromatic418967fa.accept_7_3_1_2_1_247 73 85 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 85 163 (Polychromatic418967fa.accept_10_2_5_3_1_1408 72 85 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 85 163 (accept_3_3 71 85 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 85 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 85 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 85 163 (Polychromatic418967fa.accept_7_6_1_2_1_230 69
  85 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 85 163 (accept_3_3 68 85
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 85 163
  (Polychromatic418967fa.accept_10_7_5_3_1_542 67 85 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 85 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 85 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 85 163 (accept_3_3 65 85 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 85 163 (Polychromatic418967fa.accept_14_8_1_9_1_2085 64 85 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 85 163
  (Polychromatic418967fa.accept_15_3_10_13_1_2605 63 85 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 85 163 (accept_3_3 62 85 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  85 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 61 85 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 85 163 (Polychromatic418967fa.accept_9_6_4_1_1_390 60 85 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 85 163 (accept_3_3 59 85 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 85 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 85 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 85 163
  (Polychromatic418967fa.accept_9_3_4_1_1_22 57 85 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 85 163 (accept_3_3 56 85 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  85 163 (Polychromatic418967fa.accept_7_6_1_2_1_230 55 85 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 85 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 85 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 85 163 (accept_3_3 53 85 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 85 163 (Polychromatic418967fa.accept_7_3_1_2_1_247 52 85 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 85 163
  (Polychromatic418967fa.accept_9_6_4_1_1_390 51 85 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 85 163 (accept_3_3 50 85 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  85 163 (Polychromatic418967fa.accept_15_4_10_13_1_2565 49 85 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 85 163 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 85 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 85 163 (accept_3_3 47 85 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 85 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 85 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 85 163
  (Polychromatic418967fa.accept_7_3_1_2_1_247 45 85 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 85 163 (accept_3_3 44 85 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  85 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 85 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 85 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 85 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 85 163 (accept_3_3 41 85 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 85 163 (Polychromatic418967fa.accept_16_8_5_3_1_4297 40 85 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 85 163
  (Polychromatic418967fa.accept_9_3_4_1_1_22 39 85 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 85 163 (accept_3_3 38 85 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  85 163 (Polychromatic418967fa.accept_10_7_5_3_1_542 37 85 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 85 163 (Polychromatic418967fa.accept_14_8_1_9_1_2085 36 85 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 85 163 (accept_3_3 35 85 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 85 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 85 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 85 163
  (Polychromatic418967fa.accept_9_6_4_1_1_390 33 85 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 85 163 (accept_3_3 32 85 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  85 163 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 85 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 85 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 85 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 85 163 (accept_3_3 29 85 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 85 163 (Polychromatic418967fa.accept_10_8_5_3_1_543 28 85 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 85 163
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 85 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 85 163 (accept_3_3 26 85 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  85 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 85 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 85 163 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 85 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 85 163 (accept_3_3 23 85 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 85 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 85 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 85 163
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 85 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 85 163 (accept_3_3 20 85 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  85 163 (Polychromatic418967fa.accept_15_4_10_13_1_2565 19 85 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 85 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 85 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 85 163 (accept_3_3 17 85 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 85 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 85 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 85 163
  (Polychromatic418967fa.accept_9_6_4_1_1_390 15 85 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 85 163 (accept_3_3 14 85 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  85 163 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 85 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 85 163 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 85 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 85 163 (accept_3_3 11 85 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 85 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 85 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 85 163
  (Polychromatic418967fa.accept_23_9_16_2_1_9058 9 85 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 85 163 (accept_3_3 8 85 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 85
  163 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 85 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 85 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 85 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 85 163 (accept_3_3 5 85 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 85 163 (Polychromatic418967fa.accept_15_4_10_13_1_2565 4 85 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 85 163 (Polychromatic418967fa.accept_7_3_1_2_1_247 3
  85 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 163 (accept_3_3 2 85 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 85 163 (Polychromatic418967fa.accept_15_1_10_13_1_939
  1 85 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  163))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 84 163 (Eq.refl
  Bool.true) (allA_succ_of_accept 79 84 163 (Polychromatic418967fa.accept_8_7_4_3_1_156 79 84 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 84 163 (Polychromatic418967fa.accept_9_6_3_1_1_155 78
  84 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 84 163 (accept_3_3 77 84
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 84 163
  (Polychromatic418967fa.accept_9_4_3_1_1_154 76 84 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 84 163 (Polychromatic418967fa.accept_17_7_16_10_1_1849 75 84 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 84 163 (accept_3_3 74 84 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 84 163 (Polychromatic418967fa.accept_19_16_8_11_1_6080 73 84 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 84 163
  (Polychromatic418967fa.accept_16_8_4_3_1_3146 72 84 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 84 163 (accept_3_3 71 84 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  84 163 (Polychromatic418967fa.accept_9_7_3_1_1_386 70 84 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 84 163 (Polychromatic418967fa.accept_9_6_3_1_1_155 69 84 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 84 163 (accept_3_3 68 84 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 84 163 (Polychromatic418967fa.accept_9_4_3_1_1_154 67 84 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 84 163
  (Polychromatic418967fa.accept_13_1_6_7_1_550 66 84 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 84 163 (accept_3_3 65 84 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  84 163 (Polychromatic418967fa.accept_13_12_6_7_1_1071 64 84 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 84 163 (Polychromatic418967fa.accept_8_7_4_3_1_156 63 84 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 84 163 (accept_3_3 62 84 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 84 163 (Polychromatic418967fa.accept_9_7_3_1_1_386 61 84 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 84 163
  (Polychromatic418967fa.accept_9_6_3_1_1_155 60 84 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 84 163 (accept_3_3 59 84 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  84 163 (Polychromatic418967fa.accept_9_4_3_1_1_154 58 84 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 84 163 (Polychromatic418967fa.accept_10_7_4_3_1_560 57 84 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 84 163 (accept_3_3 56 84 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 84 163 (Polychromatic418967fa.accept_8_7_4_3_1_156 55 84 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 84 163
  (Polychromatic418967fa.accept_16_6_4_3_1_2189 54 84 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 84 163 (accept_3_3 53 84 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  84 163 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 84 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 84 163 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 84 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 84 163 (accept_3_3 50 84 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 84 163 (Polychromatic418967fa.accept_9_4_3_1_1_154 49 84 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 84 163
  (Polychromatic418967fa.accept_13_9_6_7_1_551 48 84 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 84 163 (accept_3_3 47 84 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  84 163 (Polychromatic418967fa.accept_11_2_7_9_1_890 46 84 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 84 163 (Polychromatic418967fa.accept_19_7_8_11_1_3379 45 84 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 84 163 (accept_3_3 44 84 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 84 163 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 84 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 84 163
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 84 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 84 163 (accept_3_3 41 84 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  84 163 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 84 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 84 163 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 84 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 84 163 (accept_3_3 38 84 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 84 163 (Polychromatic418967fa.accept_10_7_4_3_1_560 37 84 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 84 163
  (Polychromatic418967fa.accept_19_17_8_11_1_7605 36 84 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 84 163 (accept_3_3 35 84 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  84 163 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 84 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 84 163 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 84 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 84 163 (accept_3_3 32 84 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 84 163 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 84 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 84 163
  (Polychromatic418967fa.accept_13_4_6_7_1_2471 30 84 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 84 163 (accept_3_3 29 84 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  84 163 (Polychromatic418967fa.accept_16_12_4_3_1_4295 28 84 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 84 163 (Polychromatic418967fa.accept_10_7_4_3_1_560 27 84 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 84 163 (accept_3_3 26 84 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 84 163 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 84 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 84 163
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 84 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 84 163 (accept_3_3 23 84 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  84 163 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 84 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 84 163 (Polychromatic418967fa.accept_18_3_12_1_1_3787 21 84 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 84 163 (accept_3_3 20 84 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 163 (Polychromatic418967fa.accept_10_9_4_3_1_539 19 84 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 84 163
  (Polychromatic418967fa.accept_15_3_9_13_1_1681 18 84 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 84 163 (accept_3_3 17 84 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  84 163 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 84 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 84 163 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 84 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 84 163 (accept_3_3 14 84 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 163 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 84 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 84 163
  (Polychromatic418967fa.accept_13_12_6_7_1_1071 12 84 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 84 163 (accept_3_3 11 84 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  84 163 (Polychromatic418967fa.accept_19_10_8_11_1_4708 10 84 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 84 163 (Polychromatic418967fa.accept_10_9_4_3_1_539 9 84 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 84 163 (accept_3_3 8 84 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 163 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 84 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 84 163
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 84 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 84 163 (accept_3_3 5 84 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 84
  163 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 84 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 84 163 (Polychromatic418967fa.accept_15_3_9_13_1_1681 3 84 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 84 163 (accept_3_3 2 84 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 84 163 (Polychromatic418967fa.accept_13_1_6_7_1_550 1 84 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  163)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 81 83 163 (Eq.refl
  Bool.true) (allA_of_3_1 81 83 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 82 163 (allA_succ_of_accept 81
  82 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 82 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 82 163 (accept_3_3 80 82 163 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 82 163 (Polychromatic418967fa.accept_16_15_2_3_1_4262 79 82 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 82 163 (Polychromatic418967fa.accept_20_18_2_3_1_3169 78 82
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 82 163 (accept_3_3 77 82 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 82 163 (Polychromatic418967fa.accept_12_4_10_7_1_149
  76 82 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 82 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 82 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 82 163 (accept_3_3 74 82 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  82 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 82 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 82 163 (Polychromatic418967fa.accept_19_15_6_11_1_9047 72 82 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 82 163 (accept_3_3 71 82 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 82 163 (Polychromatic418967fa.accept_16_6_2_3_1_4223 70 82 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 82 163
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 82 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 82 163 (accept_3_3 68 82 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  82 163 (Polychromatic418967fa.accept_7_4_5_2_1_243 67 82 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 82 163 (Polychromatic418967fa.accept_7_3_5_2_1_17 66 82 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 82 163 (accept_3_3 65 82 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 82 163 (Polychromatic418967fa.accept_12_4_10_7_1_149 64 82 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 82 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 82 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 82 163 (accept_3_3 62 82 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  82 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 82 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 82 163 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 82 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 82 163 (accept_3_3 59 82 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 82 163 (Polychromatic418967fa.accept_13_6_4_7_1_2464 58 82 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 82 163
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 82 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 82 163 (accept_3_3 56 82 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  82 163 (Polychromatic418967fa.accept_10_5_2_3_1_239 55 82 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 82 163 (Polychromatic418967fa.accept_15_9_7_13_1_1664 54 82 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 82 163 (accept_3_3 53 82 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 82 163 (Polychromatic418967fa.accept_7_3_5_2_1_17 52 82 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 82 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 82 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 82 163 (accept_3_3 50 82 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  82 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 82 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 82 163 (Polychromatic418967fa.accept_13_9_4_7_1_1694 48 82 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 82 163 (accept_3_3 47 82 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 82 163 (Polychromatic418967fa.accept_7_4_5_2_1_243 46 82 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 82 163
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 82 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 82 163 (accept_3_3 44 82 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  82 163 (Polychromatic418967fa.accept_19_5_6_11_1_6069 43 82 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 82 163 (Polychromatic418967fa.accept_13_3_4_7_1_1711 42 82 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 82 163 (accept_3_3 41 82 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 82 163 (Polychromatic418967fa.accept_11_7_5_9_1_884 40 82 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 82 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 82 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 82 163 (accept_3_3 38 82 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  82 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 82 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 82 163 (Polychromatic418967fa.accept_13_10_4_7_1_2465 36 82 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 82 163 (accept_3_3 35 82 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 82 163 (Polychromatic418967fa.accept_18_16_10_1_1_3696 34 82
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 82 163
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 82 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 82 163 (accept_3_3 32 82 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  82 163 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 82 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 82 163 (Polychromatic418967fa.accept_17_13_14_10_1_1847 30 82 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 82 163 (accept_3_3 29 82 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 82 163 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 82 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 82 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 82 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 82 163 (accept_3_3 26 82 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  82 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 82 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 82 163 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 82 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 82 163 (accept_3_3 23 82 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 82 163 (Polychromatic418967fa.accept_13_9_4_7_1_1694 22 82 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 82 163
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 82 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 82 163 (accept_3_3 20 82 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  82 163 (Polychromatic418967fa.accept_13_6_4_7_1_2464 19 82 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 82 163 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 82 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 82 163 (accept_3_3 17 82 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 82 163 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 82 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 82 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 82 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 82 163 (accept_3_3 14 82 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  82 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 82 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 82 163 (Polychromatic418967fa.accept_13_12_4_7_1_2520 12 82 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 82 163 (accept_3_3 11 82 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 82 163 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 82 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 82 163
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 82 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 82 163 (accept_3_3 8 82 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 82
  163 (Polychromatic418967fa.accept_11_7_5_9_1_884 7 82 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 82 163 (Polychromatic418967fa.accept_13_6_4_7_1_2464 6 82 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 82 163 (accept_3_3 5 82 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 82 163 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 82 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 82 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 82
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 163 (accept_3_3 2 82 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 82 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 82
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  163)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 81 163
  (allA_succ_of_accept 80 81 163 (accept_3_3 80 81 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  81 163 (Polychromatic418967fa.accept_11_2_4_9_1_484 79 81 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 81 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 163 (accept_3_3 77 81 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 81 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 163
  (Polychromatic418967fa.accept_7_5_4_2_1_235 75 81 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 81 163 (accept_3_3 74 81 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  81 163 (Polychromatic418967fa.accept_13_8_3_7_1_2455 73 81 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 81 163 (Polychromatic418967fa.accept_10_2_1_3_1_233 72 81 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 163 (accept_3_3 71 81 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 81 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 163
  (Polychromatic418967fa.accept_7_6_4_2_1_236 69 81 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 81 163 (accept_3_3 68 81 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  81 163 (Polychromatic418967fa.accept_15_7_6_13_1_936 67 81 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 81 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 81 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 163 (accept_3_3 65 81 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 81 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 163
  (Polychromatic418967fa.accept_12_3_9_7_1_472 63 81 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 81 163 (accept_3_3 62 81 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  81 163 (Polychromatic418967fa.accept_7_5_4_2_1_235 61 81 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 81 163 (Polychromatic418967fa.accept_13_8_3_7_1_2455 60 81 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 163 (accept_3_3 59 81 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 81 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 163
  (Polychromatic418967fa.accept_11_2_4_9_1_484 57 81 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 81 163 (accept_3_3 56 81 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  81 163 (Polychromatic418967fa.accept_7_6_4_2_1_236 55 81 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 81 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 81 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 163 (accept_3_3 53 81 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 81 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 163
  (Polychromatic418967fa.accept_12_3_9_7_1_472 51 81 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 81 163 (accept_3_3 50 81 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  81 163 (Polychromatic418967fa.accept_13_10_3_7_1_2517 49 81 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 81 163 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 81 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 163 (accept_3_3 47 81 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 81 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 163
  (Polychromatic418967fa.accept_16_13_1_3_1_2205 45 81 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 81 163 (accept_3_3 44 81 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  81 163 (Polychromatic418967fa.accept_13_4_3_7_1_2515 43 81 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 81 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 81 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 163 (accept_3_3 41 81 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 81 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 163
  (Polychromatic418967fa.accept_12_3_9_7_1_472 39 81 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 81 163 (accept_3_3 38 81 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  81 163 (Polychromatic418967fa.accept_13_11_3_7_1_2513 37 81 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 81 163 (Polychromatic418967fa.accept_13_10_3_7_1_2517 36 81 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 163 (accept_3_3 35 81 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 81 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 163
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 81 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 81 163 (accept_3_3 32 81 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  81 163 (Polychromatic418967fa.accept_17_14_13_10_1_3936 31 81 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 81 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 81 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 163 (accept_3_3 29 81 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 81 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 163
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 81 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 81 163 (accept_3_3 26 81 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  81 163 (Polychromatic418967fa.accept_19_6_5_11_1_6067 25 81 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 81 163 (Polychromatic418967fa.accept_11_2_4_9_1_484 24 81 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 163 (accept_3_3 23 81 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 81 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 163
  (Polychromatic418967fa.accept_13_8_3_7_1_2455 21 81 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 81 163 (accept_3_3 20 81 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  81 163 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 81 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 81 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 81 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 163 (accept_3_3 17 81 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 81 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 163
  (Polychromatic418967fa.accept_12_3_9_7_1_472 15 81 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 81 163 (accept_3_3 14 81 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  81 163 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 81 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 81 163 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 81 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 163 (accept_3_3 11 81 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 81 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 163
  (Polychromatic418967fa.accept_13_9_3_7_1_1065 9 81 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 81 163 (accept_3_3 8 81 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81
  163 (Polychromatic418967fa.accept_15_7_6_13_1_936 7 81 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 81 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 81 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 163 (accept_3_3 5 81 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 81 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 163
  (Polychromatic418967fa.accept_12_3_9_7_1_472 3 81 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 81 163 (accept_3_3 2 81 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81
  163 (Polychromatic418967fa.accept_13_1_3_7_1_1710 1 81 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 81 163)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 80 163 (allA_of_3_1 80 80 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 79 163
  (allA_succ_of_accept 78 79 163 (Polychromatic418967fa.accept_9_6_7_1_1_145 78 79 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 79 163 (accept_3_3 77 79 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 79 163 (Polychromatic418967fa.accept_8_4_7_3_1_144 76 79 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 79 163 (Polychromatic418967fa.accept_9_3_7_1_1_143 75
  79 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 79 163 (accept_3_3 74 79
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 79 163
  (Polychromatic418967fa.accept_11_7_2_9_1_480 73 79 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 79 163 (Polychromatic418967fa.accept_17_4_11_10_1_5167 72 79 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 79 163 (accept_3_3 71 79 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 79 163 (Polychromatic418967fa.accept_11_4_2_9_1_496 70 79 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 79 163 (Polychromatic418967fa.accept_9_6_7_1_1_145 69
  79 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 79 163 (accept_3_3 68 79
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 79 163
  (Polychromatic418967fa.accept_9_4_7_1_1_379 67 79 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 79 163 (Polychromatic418967fa.accept_9_3_7_1_1_143 66 79 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 79 163 (accept_3_3 65 79 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 79 163 (Polychromatic418967fa.accept_10_4_9_3_1_1907 64 79 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 79 163 (Polychromatic418967fa.accept_13_11_1_7_1_1691
  63 79 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 79 163 (accept_3_3 62
  79 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 79 163
  (Polychromatic418967fa.accept_16_13_15_3_1_4196 61 79 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 79 163 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 79 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 79 163 (accept_3_3 59 79 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 79 163 (Polychromatic418967fa.accept_9_4_7_1_1_379 58 79 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 79 163 (Polychromatic418967fa.accept_9_3_7_1_1_143 57
  79 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 79 163 (accept_3_3 56 79
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 79 163
  (Polychromatic418967fa.accept_13_3_1_7_1_1706 55 79 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 79 163 (Polychromatic418967fa.accept_10_4_9_3_1_1907 54 79 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 79 163 (accept_3_3 53 79 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 79 163 (Polychromatic418967fa.accept_8_4_7_3_1_144 52 79 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 79 163 (Polychromatic418967fa.accept_9_6_7_1_1_145 51
  79 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 79 163 (accept_3_3 50 79
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 79 163
  (Polychromatic418967fa.accept_9_4_7_1_1_379 49 79 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 79 163 (Polychromatic418967fa.accept_9_3_7_1_1_143 48 79 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 79 163 (accept_3_3 47 79 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 79 163 (Polychromatic418967fa.accept_10_6_9_3_1_935 46 79 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 79 163 (Polychromatic418967fa.accept_13_6_1_7_1_1690
  45 79 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 79 163 (accept_3_3 44
  79 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 79 163
  (Polychromatic418967fa.accept_16_11_15_3_1_1304 43 79 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 79 163 (Polychromatic418967fa.accept_9_6_7_1_1_145 42 79 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 79 163 (accept_3_3 41 79 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 79 163 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 79 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 79 163 (Polychromatic418967fa.accept_9_3_7_1_1_143 39
  79 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 79 163 (accept_3_3 38 79
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 79 163
  (Polychromatic418967fa.accept_11_4_2_9_1_496 37 79 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 79 163 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 79 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 79 163 (accept_3_3 35 79 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 79 163 (Polychromatic418967fa.accept_10_4_9_3_1_1907 34 79 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 79 163 (Polychromatic418967fa.accept_9_6_7_1_1_145 33
  79 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 79 163 (accept_3_3 32 79
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 79 163
  (Polychromatic418967fa.accept_9_4_7_1_1_379 31 79 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 79 163 (Polychromatic418967fa.accept_9_3_7_1_1_143 30 79 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 79 163 (accept_3_3 29 79 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 79 163 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 79 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 79 163
  (Polychromatic418967fa.accept_16_11_15_3_1_1304 27 79 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 79 163 (accept_3_3 26 79 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  79 163 (Polychromatic418967fa.accept_15_10_4_13_1_4506 25 79 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 79 163 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 79 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 79 163 (accept_3_3 23 79 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 79 163 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 79 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 79 163
  (Polychromatic418967fa.accept_9_3_7_1_1_143 21 79 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 79 163 (accept_3_3 20 79 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  79 163 (Polychromatic418967fa.accept_13_6_1_7_1_1690 19 79 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 79 163 (Polychromatic418967fa.accept_11_7_2_9_1_480 18 79 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 79 163 (accept_3_3 17 79 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 79 163 (Polychromatic418967fa.accept_10_6_9_3_1_935 16 79 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 79 163
  (Polychromatic418967fa.accept_9_6_7_1_1_145 15 79 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 79 163 (accept_3_3 14 79 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  79 163 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 79 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 79 163 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 79 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 79 163 (accept_3_3 11 79 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 79 163 (Polychromatic418967fa.accept_15_10_4_13_1_4506 10 79 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 79 163
  (Polychromatic418967fa.accept_15_9_4_13_1_4482 9 79 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 79 163 (accept_3_3 8 79 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 79
  163 (Polychromatic418967fa.accept_11_7_2_9_1_480 7 79 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 79 163 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 79 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 79 163 (accept_3_3 5 79 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 79 163 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 79 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 79 163 (Polychromatic418967fa.accept_9_3_7_1_1_143 3
  79 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 163 (accept_3_3 2 79 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 79 163 (Polychromatic418967fa.accept_17_1_11_10_1_5149
  1 79 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79
  163))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 78 163
  (allA_succ_of_accept 77 78 163 (accept_3_3 77 78 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  78 163 (Polychromatic418967fa.accept_7_6_1_2_1_230 76 78 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 78 163 (Polychromatic418967fa.accept_9_3_6_1_1_24 75 78 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 78 163 (accept_3_3 74 78 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 78 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 78 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 78 163
  (Polychromatic418967fa.accept_15_12_3_13_1_4481 72 78 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 78 163 (accept_3_3 71 78 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  78 163 (Polychromatic418967fa.accept_9_7_6_1_1_709 70 78 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 78 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 78 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 78 163 (accept_3_3 68 78 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 163 (Polychromatic418967fa.accept_9_4_6_1_1_393 67 78 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 78 163
  (Polychromatic418967fa.accept_7_3_1_2_1_247 66 78 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 78 163 (accept_3_3 65 78 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  78 163 (Polychromatic418967fa.accept_21_1_15_16_1_5891 64 78 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 78 163 (Polychromatic418967fa.accept_18_9_6_1_1_3687 63 78 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 78 163 (accept_3_3 62 78 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 78 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 78 163
  (Polychromatic418967fa.accept_19_3_2_11_1_7647 60 78 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 78 163 (accept_3_3 59 78 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  78 163 (Polychromatic418967fa.accept_9_4_6_1_1_393 58 78 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 78 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 78 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 78 163 (accept_3_3 56 78 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 78 163 (Polychromatic418967fa.accept_7_6_1_2_1_230 55 78 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 78 163
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 54 78 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 78 163 (accept_3_3 53 78 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  78 163 (Polychromatic418967fa.accept_7_3_1_2_1_247 52 78 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 78 163 (Polychromatic418967fa.accept_10_1_8_3_1_947 51 78 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 78 163 (accept_3_3 50 78 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 78 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 78 163
  (Polychromatic418967fa.accept_7_6_1_2_1_230 48 78 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 78 163 (accept_3_3 47 78 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  78 163 (Polychromatic418967fa.accept_10_6_8_3_1_930 46 78 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 78 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 78 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 78 163 (accept_3_3 44 78 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 163 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 78 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 78 163
  (Polychromatic418967fa.accept_15_12_3_13_1_4481 42 78 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 78 163 (accept_3_3 41 78 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  78 163 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 78 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 78 163 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 78 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 78 163 (accept_3_3 38 78 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 78 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 78 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 78 163
  (Polychromatic418967fa.accept_10_6_8_3_1_930 36 78 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 78 163 (accept_3_3 35 78 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  78 163 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 78 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 78 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 78 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 78 163 (accept_3_3 32 78 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 163 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 78 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 78 163
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 78 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 78 163 (accept_3_3 29 78 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  78 163 (Polychromatic418967fa.accept_19_9_2_11_1_7581 28 78 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 78 163 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 78 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 78 163 (accept_3_3 26 78 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 78 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 78 163
  (Polychromatic418967fa.accept_7_3_1_2_1_247 24 78 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 78 163 (accept_3_3 23 78 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  78 163 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 78 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 78 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 78 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 78 163 (accept_3_3 20 78 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 163 (Polychromatic418967fa.accept_22_19_12_9_1_9057 19 78 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 163
  (Polychromatic418967fa.accept_21_18_15_16_1_2917 18 78 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 78 163 (accept_3_3 17 78 163 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 78 163 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 78 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 78 163 (Polychromatic418967fa.accept_10_5_8_3_1_229 15 78 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 78 163 (accept_3_3 14 78 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 13
  78 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 78 163
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 78 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 78 163 (accept_3_3 11 78 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  78 163 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 78 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 78 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 78 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 78 163 (accept_3_3 8 78 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 163 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 78 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 78 163
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 78 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 78 163 (accept_3_3 5 78 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78
  163 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 78 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 78 163 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 78 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 78 163 (accept_3_3 2 78 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 78 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 78 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  163)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 163 (allA_of_3_1 77 77
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 76 163 (allA_succ_of_accept 75 76 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 76 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 76 163 (accept_3_3 74 76 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  76 163 (Polychromatic418967fa.accept_7_3_6_2_1_90 73 76 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 76 163 (Polychromatic418967fa.accept_15_12_1_13_1_3444 72 76 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 76 163 (accept_3_3 71 76 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 76 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 70 76 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 76 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 76 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 76 163 (accept_3_3 68 76 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  76 163 (Polychromatic418967fa.accept_7_4_6_2_1_451 67 76 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 76 163 (Polychromatic418967fa.accept_7_3_6_2_1_90 66 76 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 76 163 (accept_3_3 65 76 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 76 163 (Polychromatic418967fa.accept_7_1_6_2_1_18 64 76 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 76 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 76 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 76 163 (accept_3_3 62 76 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  76 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 61 76 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 76 163 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 76 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 76 163 (accept_3_3 59 76 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 76 163 (Polychromatic418967fa.accept_10_8_6_3_1_1394 58 76 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 76 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 76 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 76 163 (accept_3_3 56 76 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  76 163 (Polychromatic418967fa.accept_8_7_4_3_1_156 55 76 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 76 163 (Polychromatic418967fa.accept_26_2_24_7_1_9056 54 76 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 76 163 (accept_3_3 53 76 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 76 163 (Polychromatic418967fa.accept_7_3_6_2_1_90 52 76 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 76 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 76 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 76 163 (accept_3_3 50 76 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  76 163 (Polychromatic418967fa.accept_10_9_6_3_1_545 49 76 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 76 163 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 76 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 76 163 (accept_3_3 47 76 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 76 163 (Polychromatic418967fa.accept_7_4_6_2_1_451 46 76 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 76 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 76 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 76 163 (accept_3_3 44 76 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  76 163 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 76 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 76 163 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 76 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 76 163 (accept_3_3 41 76 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 76 163 (Polychromatic418967fa.accept_13_1_11_7_1_1704 40 76 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 76 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 76 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 76 163 (accept_3_3 38 76 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  76 163 (Polychromatic418967fa.accept_10_7_6_3_1_927 37 76 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 76 163 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 76 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 76 163 (accept_3_3 35 76 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 76 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 76 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 76 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 76 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 76 163 (accept_3_3 32 76 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  76 163 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 76 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 76 163 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 76 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 76 163 (accept_3_3 29 76 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 76 163 (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 76 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 76 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 76 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 76 163 (accept_3_3 26 76 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  76 163 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 76 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 76 163 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 76 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 76 163 (accept_3_3 23 76 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 76 163 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 76 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 76 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 76 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 76 163 (accept_3_3 20 76 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  76 163 (Polychromatic418967fa.accept_10_9_6_3_1_545 19 76 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 76 163 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 76 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 76 163 (accept_3_3 17 76 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 76 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 76 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 76 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 76 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 76 163 (accept_3_3 14 76 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  76 163 (Polychromatic418967fa.accept_20_13_16_3_1_4479 13 76 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 76 163 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 76 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 76 163 (accept_3_3 11 76 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 76 163 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 76 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 76 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 76 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 76 163 (accept_3_3 8 76 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 76
  163 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 76 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 76 163 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 76 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 76 163 (accept_3_3 5 76 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 76 163 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 76 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 76 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 76
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 76 163 (accept_3_3 2 76 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 76 163 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 76
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76
  163)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 163 (allA_succ_of_accept
  74 75 163 (accept_3_3 74 75 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 75 163
  (Polychromatic418967fa.accept_7_3_5_2_1_17 73 75 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 75 163 (Polychromatic418967fa.accept_10_2_5_3_1_1408 72 75 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 75 163 (accept_3_3 71 75 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 75 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 75 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 163 (Polychromatic418967fa.accept_9_6_3_1_1_155 69
  75 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 163 (accept_3_3 68 75
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 163
  (Polychromatic418967fa.accept_7_4_5_2_1_243 67 75 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 75 163 (Polychromatic418967fa.accept_7_3_5_2_1_17 66 75 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 75 163 (accept_3_3 65 75 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 75 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 75 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 163 (Polychromatic418967fa.accept_14_7_5_9_1_2911
  63 75 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 163 (accept_3_3 62
  75 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 75 163
  (Polychromatic418967fa.accept_9_7_3_1_1_386 61 75 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 75 163 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 75 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 75 163 (accept_3_3 59 75 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 75 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 75 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 163 (Polychromatic418967fa.accept_10_7_5_3_1_542
  57 75 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 163 (accept_3_3 56
  75 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 75 163
  (Polychromatic418967fa.accept_13_3_10_7_1_1061 55 75 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 75 163 (Polychromatic418967fa.accept_16_6_11_3_1_2198 54 75 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 75 163 (accept_3_3 53 75 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 75 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 75 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 163 (Polychromatic418967fa.accept_9_6_3_1_1_155 51
  75 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 163 (accept_3_3 50 75
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 75 163
  (Polychromatic418967fa.accept_9_4_3_1_1_154 49 75 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 75 163 (Polychromatic418967fa.accept_10_8_5_3_1_543 48 75 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 75 163 (accept_3_3 47 75 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 75 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 75 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 163 (Polychromatic418967fa.accept_7_3_5_2_1_17 45
  75 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 163 (accept_3_3 44 75
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 163
  (Polychromatic418967fa.accept_9_7_3_1_1_386 43 75 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 75 163 (Polychromatic418967fa.accept_9_6_3_1_1_155 42 75 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 75 163 (accept_3_3 41 75 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 75 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 75 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 163 (Polychromatic418967fa.accept_7_4_5_2_1_243 39
  75 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 163 (accept_3_3 38 75
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 163
  (Polychromatic418967fa.accept_10_7_5_3_1_542 37 75 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 75 163 (Polychromatic418967fa.accept_19_17_18_11_1_2215 36 75 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 75 163 (accept_3_3 35 75 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 75 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 75 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 163 (Polychromatic418967fa.accept_9_6_3_1_1_155 33
  75 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 163 (accept_3_3 32 75
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 163 (Polychromatic418967fa.accept_7_3_5_2_1_17
  31 75 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 75 163
  (Polychromatic418967fa.accept_13_4_10_7_1_1701 30 75 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 75 163 (accept_3_3 29 75 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  75 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 75 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 75 163 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 75 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 163 (accept_3_3 26 75 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 163 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 75 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 75 163
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 75 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 75 163 (accept_3_3 23 75 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  75 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 75 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 75 163 (Polychromatic418967fa.accept_12_9_3_7_1_924 21 75 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 163 (accept_3_3 20 75 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 163 (Polychromatic418967fa.accept_23_19_6_2_1_9055 19 75 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 163
  (Polychromatic418967fa.accept_7_4_5_2_1_243 18 75 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 75 163 (accept_3_3 17 75 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  75 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 75 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 75 163 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 75 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 163 (accept_3_3 14 75 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 163 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 75 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 75 163
  (Polychromatic418967fa.accept_10_2_5_3_1_1408 12 75 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 75 163 (accept_3_3 11 75 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  75 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 75 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 75 163 (Polychromatic418967fa.accept_12_9_3_7_1_924 9 75 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 163 (accept_3_3 8 75 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 163 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 75 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 163
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 75 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 163 (accept_3_3 5 75 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75
  163 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 75 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 75 163 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 75 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 163 (accept_3_3 2 75 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 75 163 (Polychromatic418967fa.accept_17_1_7_10_1_1835 1 75 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  163))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 163 (allA_of_3_1 74 74
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 73 163 (allA_succ_of_accept 72 73 163
  (Polychromatic418967fa.accept_19_15_16_11_1_7689 72 73 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 73 163 (accept_3_3 71 73 163 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 73 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 73 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 73 163 (Polychromatic418967fa.accept_7_6_3_2_1_461 69 73 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 163 (accept_3_3 68 73 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 163 (Polychromatic418967fa.accept_13_2_8_7_1_2424
  67 73 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 163
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 73 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 73 163 (accept_3_3 65 73 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  73 163 (Polychromatic418967fa.accept_7_1_3_2_1_13 64 73 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 73 163 (Polychromatic418967fa.accept_17_12_5_10_1_5160 63 73 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 163 (accept_3_3 62 73 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 163 (Polychromatic418967fa.accept_7_5_3_2_1_249 61 73 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 163
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 60 73 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 163 (accept_3_3 59 73 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 73 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 163 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 73 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 163 (accept_3_3 56 73 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 163 (Polychromatic418967fa.accept_7_6_3_2_1_461 55 73 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 163
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 73 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 163 (accept_3_3 53 73 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 163 (Polychromatic418967fa.accept_19_14_16_11_1_9054 52 73 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 163 (Polychromatic418967fa.accept_13_12_8_7_1_2526 51 73 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 163 (accept_3_3 50 73 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 163 (Polychromatic418967fa.accept_11_5_7_9_1_2696 49 73 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 163
  (Polychromatic418967fa.accept_7_6_3_2_1_461 48 73 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 163 (accept_3_3 47 73 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 73 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 163 (Polychromatic418967fa.accept_21_3_10_16_1_4340 45 73 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 163 (accept_3_3 44 73 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 163 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 73 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 163
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 73 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 163 (accept_3_3 41 73 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 163 (Polychromatic418967fa.accept_7_5_3_2_1_249 40 73 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 163 (Polychromatic418967fa.accept_16_7_9_3_1_1324 39 73 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 163 (accept_3_3 38 73 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 163 (Polychromatic418967fa.accept_22_15_7_9_1_9053 37 73 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 163
  (Polychromatic418967fa.accept_7_1_3_2_1_13 36 73 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 163 (accept_3_3 35 73 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 73 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 163 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 73 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 163 (accept_3_3 32 73 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 163 (Polychromatic418967fa.accept_17_14_5_10_1_9052 31 73 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 163
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 73 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 163 (accept_3_3 29 73 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 163 (Polychromatic418967fa.accept_13_2_8_7_1_2424 28 73 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 163 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 73 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 163 (accept_3_3 26 73 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 163 (Polychromatic418967fa.accept_13_12_8_7_1_2526 25 73 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 163
  (Polychromatic418967fa.accept_11_2_7_9_1_890 24 73 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 163 (accept_3_3 23 73 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 73 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 163 (Polychromatic418967fa.accept_19_2_16_11_1_6045 21 73 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 163 (accept_3_3 20 73 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 163 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 73 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 163
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 73 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 163 (accept_3_3 17 73 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 163 (Polychromatic418967fa.accept_11_5_7_9_1_2696 16 73 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 163 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 73 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 163 (accept_3_3 14 73 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 163 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 73 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 163
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 73 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 163 (accept_3_3 11 73 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 73 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 163 (Polychromatic418967fa.accept_13_9_8_7_1_1073 9 73 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 163 (accept_3_3 8 73 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 163 (Polychromatic418967fa.accept_16_7_9_3_1_1324 7 73 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 163
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 73 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 163 (accept_3_3 5 73 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  163 (Polychromatic418967fa.accept_19_4_16_11_1_6046 4 73 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 73 163 (Polychromatic418967fa.accept_13_3_8_7_1_4135 3 73 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 163 (accept_3_3 2 73 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 73 163 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 73 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  163))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 163 (allA_succ_of_accept 71
  72 163 (accept_3_3 71 72 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 72 163
  (Polychromatic418967fa.accept_15_10_12_13_1_2585 70 72 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 72 163 (Polychromatic418967fa.accept_11_3_6_9_1_1378 69 72 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 72 163 (accept_3_3 68 72 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 72 163 (Polychromatic418967fa.accept_14_11_2_9_1_5873 67 72 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 72 163
  (Polychromatic418967fa.accept_17_15_4_10_1_3968 66 72 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 72 163 (accept_3_3 65 72 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  72 163 (Polychromatic418967fa.accept_19_7_15_11_1_3420 64 72 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 72 163 (Polychromatic418967fa.accept_14_7_2_9_1_2093 63 72 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 72 163 (accept_3_3 62 72 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 163 (Polychromatic418967fa.accept_10_1_2_3_1_1910 61 72 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 72 163
  (Polychromatic418967fa.accept_14_4_2_9_1_2092 60 72 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 72 163 (accept_3_3 59 72 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  72 163 (Polychromatic418967fa.accept_11_3_6_9_1_1378 58 72 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 72 163 (Polychromatic418967fa.accept_17_6_4_10_1_5176 57 72 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 72 163 (accept_3_3 56 72 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 163 (Polychromatic418967fa.accept_10_5_2_3_1_239 55 72 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 72 163
  (Polychromatic418967fa.accept_19_16_15_11_1_7684 54 72 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 72 163 (accept_3_3 53 72 163 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 72 163 (Polychromatic418967fa.accept_16_4_8_3_1_4206 52 72 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 72 163 (Polychromatic418967fa.accept_10_1_2_3_1_1910 51 72 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 72 163 (accept_3_3 50 72 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 72 163 (Polychromatic418967fa.accept_14_7_2_9_1_2093
  49 72 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 72 163
  (Polychromatic418967fa.accept_15_3_12_13_1_2549 48 72 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 72 163 (accept_3_3 47 72 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  72 163 (Polychromatic418967fa.accept_14_4_2_9_1_2092 46 72 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 72 163 (Polychromatic418967fa.accept_10_5_2_3_1_239 45 72 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 72 163 (accept_3_3 44 72 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 163 (Polychromatic418967fa.accept_16_11_8_3_1_3183 43 72 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 72 163
  (Polychromatic418967fa.accept_19_4_15_11_1_7498 42 72 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 72 163 (accept_3_3 41 72 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  72 163 (Polychromatic418967fa.accept_15_10_12_13_1_2585 40 72 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 72 163 (Polychromatic418967fa.accept_14_11_2_9_1_5873 39 72 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 72 163 (accept_3_3 38 72 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 163 (Polychromatic418967fa.accept_16_5_8_3_1_4240 37 72 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 72 163
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 72 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 72 163 (accept_3_3 35 72 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  72 163 (Polychromatic418967fa.accept_21_13_9_16_1_5860 34 72 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 72 163 (Polychromatic418967fa.accept_15_3_12_13_1_2549 33 72 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 72 163 (accept_3_3 32 72 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 72 163 (Polychromatic418967fa.accept_10_1_2_3_1_1910 31 72 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 72 163
  (Polychromatic418967fa.accept_20_10_12_3_1_6003 30 72 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 72 163 (accept_3_3 29 72 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  72 163 (Polychromatic418967fa.accept_16_12_8_3_1_4241 28 72 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 72 163 (Polychromatic418967fa.accept_16_11_8_3_1_3183 27 72 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 72 163 (accept_3_3 26 72 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 163 (Polychromatic418967fa.accept_10_5_2_3_1_239 25 72 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 72 163
  (Polychromatic418967fa.accept_19_5_15_11_1_7568 24 72 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 72 163 (accept_3_3 23 72 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  72 163 (Polychromatic418967fa.accept_23_22_3_2_1_9051 22 72 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 72 163 (Polychromatic418967fa.accept_10_1_2_3_1_1910 21 72 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 72 163 (accept_3_3 20 72 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 163 (Polychromatic418967fa.accept_22_19_6_9_1_9026 19 72 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 72 163
  (Polychromatic418967fa.accept_14_4_2_9_1_2092 18 72 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 72 163 (accept_3_3 17 72 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  72 163 (Polychromatic418967fa.accept_15_1_12_13_1_944 16 72 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 72 163 (Polychromatic418967fa.accept_10_5_2_3_1_239 15 72 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 72 163 (accept_3_3 14 72 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 163 (Polychromatic418967fa.accept_16_13_8_3_1_5374 13 72 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 72 163
  (Polychromatic418967fa.accept_16_12_8_3_1_4241 12 72 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 72 163 (accept_3_3 11 72 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  72 163 (Polychromatic418967fa.accept_15_10_12_13_1_2585 10 72 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 72 163 (Polychromatic418967fa.accept_19_9_15_11_1_7687 9 72 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 72 163 (accept_3_3 8 72 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 163 (Polychromatic418967fa.accept_14_7_2_9_1_2093 7 72 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 72 163
  (Polychromatic418967fa.accept_17_6_4_10_1_5176 6 72 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 72 163 (accept_3_3 5 72 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 72
  163 (Polychromatic418967fa.accept_14_4_2_9_1_2092 4 72 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 72 163 (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 72 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 72 163 (accept_3_3 2 72 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 163 (Polychromatic418967fa.accept_10_1_2_3_1_1910 1 72 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72
  163)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 163 (allA_of_3_1 71 71 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 70 163 (allA_succ_of_accept 69 70 163
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 70 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 70 163 (accept_3_3 68 70 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  70 163 (Polychromatic418967fa.accept_9_4_7_1_1_379 67 70 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 70 163 (Polychromatic418967fa.accept_9_3_7_1_1_143 66 70 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 70 163 (accept_3_3 65 70 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 70 163 (Polychromatic418967fa.accept_12_4_10_7_1_149 64 70 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 70 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 70 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 70 163 (accept_3_3 62 70 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  70 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 70 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 70 163 (Polychromatic418967fa.accept_9_6_7_1_1_145 60 70 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 70 163 (accept_3_3 59 70 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 70 163 (Polychromatic418967fa.accept_9_4_7_1_1_379 58 70 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 70 163
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 70 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 70 163 (accept_3_3 56 70 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  70 163 (Polychromatic418967fa.accept_19_17_13_11_1_2222 55 70 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 70 163 (Polychromatic418967fa.accept_13_2_5_7_1_1695 54 70 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 70 163 (accept_3_3 53 70 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 70 163 (Polychromatic418967fa.accept_12_4_10_7_1_149 52 70 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 70 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 70 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 70 163 (accept_3_3 50 70 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  70 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 70 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 70 163 (Polychromatic418967fa.accept_9_3_7_1_1_143 48 70 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 70 163 (accept_3_3 47 70 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 70 163 (Polychromatic418967fa.accept_11_2_4_9_1_484 46 70 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 70 163
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 70 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 70 163 (accept_3_3 44 70 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  70 163 (Polychromatic418967fa.accept_16_11_6_3_1_6564 43 70 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 70 163 (Polychromatic418967fa.accept_9_6_7_1_1_145 42 70 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 70 163 (accept_3_3 41 70 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 70 163 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 70 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 70 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 70 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 70 163 (accept_3_3 38 70 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  70 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 70 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 70 163 (Polychromatic418967fa.accept_16_4_6_3_1_1311 36 70 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 70 163 (accept_3_3 35 70 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 70 163 (Polychromatic418967fa.accept_15_4_10_13_1_2565 34 70 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 70 163
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 70 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 70 163 (accept_3_3 32 70 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  70 163 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 70 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 70 163 (Polychromatic418967fa.accept_9_3_7_1_1_143 30 70 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 70 163 (accept_3_3 29 70 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 70 163 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 70 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 70 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 70 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 70 163 (accept_3_3 26 70 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  70 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 70 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 70 163 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 70 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 70 163 (accept_3_3 23 70 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 70 163 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 70 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 70 163
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 70 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 70 163 (accept_3_3 20 70 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  70 163 (Polychromatic418967fa.accept_15_4_10_13_1_2565 19 70 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 70 163 (Polychromatic418967fa.accept_15_3_10_13_1_2605 18 70 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 70 163 (accept_3_3 17 70 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 70 163 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 70 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 70 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 70 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 70 163 (accept_3_3 14 70 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  70 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 70 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 70 163 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 70 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 70 163 (accept_3_3 11 70 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 70 163 (Polychromatic418967fa.accept_18_10_16_1_1_1534 10 70 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 70 163
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 70 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 70 163 (accept_3_3 8 70 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 70
  163 (Polychromatic418967fa.accept_18_7_16_1_1_4951 7 70 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 70 163 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 70 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 70 163 (accept_3_3 5 70 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 70 163 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 70 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 70 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 70 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 70 163 (accept_3_3 2 70 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 70
  163 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 70 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 70 163)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 163
  (allA_succ_of_accept 68 69 163 (accept_3_3 68 69 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  69 163 (Polychromatic418967fa.accept_7_4_6_2_1_451 67 69 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 69 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 69 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 69 163 (accept_3_3 65 69 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 69 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 163
  (Polychromatic418967fa.accept_12_3_9_7_1_472 63 69 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 69 163 (accept_3_3 62 69 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  69 163 (Polychromatic418967fa.accept_9_7_6_1_1_709 61 69 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 69 163 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 69 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 69 163 (accept_3_3 59 69 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 69 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 163
  (Polychromatic418967fa.accept_7_1_6_2_1_18 57 69 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 69 163 (accept_3_3 56 69 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  69 163 (Polychromatic418967fa.accept_13_3_4_7_1_1711 55 69 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 69 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 69 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 69 163 (accept_3_3 53 69 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 69 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 163
  (Polychromatic418967fa.accept_12_3_9_7_1_472 51 69 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 69 163 (accept_3_3 50 69 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  69 163 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 69 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 69 163 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 69 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 69 163 (accept_3_3 47 69 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 69 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 163
  (Polychromatic418967fa.accept_7_3_6_2_1_90 45 69 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 69 163 (accept_3_3 44 69 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  69 163 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 69 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 69 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 69 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 69 163 (accept_3_3 41 69 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 69 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 163
  (Polychromatic418967fa.accept_7_4_6_2_1_451 39 69 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 69 163 (accept_3_3 38 69 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  69 163 (Polychromatic418967fa.accept_13_11_4_7_1_2419 37 69 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 69 163 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 69 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 69 163 (accept_3_3 35 69 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 69 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 163
  (Polychromatic418967fa.accept_15_3_9_13_1_1681 33 69 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 69 163 (accept_3_3 32 69 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  69 163 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 69 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 69 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 69 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 163 (accept_3_3 29 69 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 69 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 163
  (Polychromatic418967fa.accept_12_3_9_7_1_472 27 69 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 69 163 (accept_3_3 26 69 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  69 163 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 69 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 69 163 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 69 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 163 (accept_3_3 23 69 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 69 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 163
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 69 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 69 163 (accept_3_3 20 69 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  69 163 (Polychromatic418967fa.accept_13_6_4_7_1_2464 19 69 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 69 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 69 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 163 (accept_3_3 17 69 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 69 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 163
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 69 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 69 163 (accept_3_3 14 69 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  69 163 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 69 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 69 163 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 69 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 163 (accept_3_3 11 69 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 69 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 163
  (Polychromatic418967fa.accept_13_9_4_7_1_1694 9 69 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 69 163 (accept_3_3 8 69 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69
  163 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 69 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 69 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 69 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 163 (accept_3_3 5 69 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 69 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 69 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 163 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 69
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 163 (accept_3_3 2 69 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 163 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 69
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  163))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 163 (allA_of_3_1 68 68 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 67 163 (allA_succ_of_accept 66 67 163
  (Polychromatic418967fa.accept_9_3_4_1_1_22 66 67 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 163 (accept_3_3 65 67 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 163 (Polychromatic418967fa.accept_10_4_7_3_1_54 64 67 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 163 (Polychromatic418967fa.accept_27_9_13_1_1_9050 63 67 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 163 (accept_3_3 62 67 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 163 (Polychromatic418967fa.accept_7_5_4_2_1_235 61 67 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 163
  (Polychromatic418967fa.accept_9_6_4_1_1_390 60 67 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 163 (accept_3_3 59 67 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 163 (Polychromatic418967fa.accept_14_2_11_9_1_2925 58 67 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 163 (Polychromatic418967fa.accept_9_3_4_1_1_22 57 67 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 163 (accept_3_3 56 67 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 163 (Polychromatic418967fa.accept_7_6_4_2_1_236 55 67 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 163
  (Polychromatic418967fa.accept_7_5_4_2_1_235 54 67 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 163 (accept_3_3 53 67 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 67 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 163 (Polychromatic418967fa.accept_9_6_4_1_1_390 51 67 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 163 (accept_3_3 50 67 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 163 (Polychromatic418967fa.accept_21_7_4_16_1_5888 49 67 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 163
  (Polychromatic418967fa.accept_7_6_4_2_1_236 48 67 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 163 (accept_3_3 47 67 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 163 (Polychromatic418967fa.accept_10_6_7_3_1_547 46 67 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 163 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 67 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 163 (accept_3_3 44 67 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 67 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 163
  (Polychromatic418967fa.accept_9_6_4_1_1_390 42 67 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 163 (accept_3_3 41 67 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 163 (Polychromatic418967fa.accept_7_5_4_2_1_235 40 67 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 163 (Polychromatic418967fa.accept_9_3_4_1_1_22 39 67 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 163 (accept_3_3 38 67 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 163 (Polychromatic418967fa.accept_19_18_10_11_1_6058 37 67 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 163
  (Polychromatic418967fa.accept_10_6_7_3_1_547 36 67 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 163 (accept_3_3 35 67 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 163 (Polychromatic418967fa.accept_7_6_4_2_1_236 34 67 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 163 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 67 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 163 (accept_3_3 32 67 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 163 (Polychromatic418967fa.accept_13_5_2_7_1_2414 31 67 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 163
  (Polychromatic418967fa.accept_9_3_4_1_1_22 30 67 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 163 (accept_3_3 29 67 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 163 (Polychromatic418967fa.accept_18_10_13_1_1_7736 28 67 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 163 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 67 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 163 (accept_3_3 26 67 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 67 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 163
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 67 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 163 (accept_3_3 23 67 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 163 (Polychromatic418967fa.accept_13_9_2_7_1_1083 22 67 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 163 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 67 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 163 (accept_3_3 20 67 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 163 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 67 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 163
  (Polychromatic418967fa.accept_13_5_2_7_1_2414 18 67 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 163 (accept_3_3 17 67 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 67 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 163 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 67 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 163 (accept_3_3 14 67 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 163 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 67 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 163
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 67 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 163 (accept_3_3 11 67 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 163 (Polychromatic418967fa.accept_11_10_1_9_1_2060 10 67 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 163 (Polychromatic418967fa.accept_13_9_2_7_1_1083 9 67 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 163 (accept_3_3 8 67 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 67 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 163
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 67 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 163 (accept_3_3 5 67 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  163 (Polychromatic418967fa.accept_10_4_7_3_1_54 4 67 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 67 163 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 67 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 163 (accept_3_3 2 67 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 67 163 (Polychromatic418967fa.accept_19_1_10_11_1_4721 1 67 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  163))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 163 (allA_succ_of_accept 65 66
  163 (accept_3_3 65 66 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 66 163
  (Polychromatic418967fa.accept_7_1_3_2_1_13 64 66 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 66 163 (Polychromatic418967fa.accept_13_11_1_7_1_1691 63 66 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 66 163 (accept_3_3 62 66 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 66 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 66 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 66 163 (Polychromatic418967fa.accept_9_6_3_1_1_155 60
  66 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 66 163 (accept_3_3 59 66
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 66 163
  (Polychromatic418967fa.accept_9_4_3_1_1_154 58 66 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 66 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 66 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 66 163 (accept_3_3 56 66 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 66 163 (Polychromatic418967fa.accept_7_6_3_2_1_461 55 66 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 66 163 (Polychromatic418967fa.accept_7_5_3_2_1_249 54
  66 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 66 163 (accept_3_3 53 66
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 66 163
  (Polychromatic418967fa.accept_9_7_3_1_1_386 52 66 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 66 163 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 66 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 66 163 (accept_3_3 50 66 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 66 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 66 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 66 163 (Polychromatic418967fa.accept_7_6_3_2_1_461 48
  66 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 66 163 (accept_3_3 47 66
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 66 163
  (Polychromatic418967fa.accept_19_8_9_11_1_9049 46 66 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 66 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 66 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 66 163 (accept_3_3 44 66 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 66 163 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 66 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 66 163 (Polychromatic418967fa.accept_9_6_3_1_1_155 42
  66 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 66 163 (accept_3_3 41 66
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 66 163
  (Polychromatic418967fa.accept_7_5_3_2_1_249 40 66 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 66 163 (Polychromatic418967fa.accept_10_9_6_3_1_545 39 66 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 66 163 (accept_3_3 38 66 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 66 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 66 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 66 163 (Polychromatic418967fa.accept_7_1_3_2_1_13 36
  66 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 66 163 (accept_3_3 35 66
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 66 163
  (Polychromatic418967fa.accept_7_6_3_2_1_461 34 66 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 66 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 66 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 66 163 (accept_3_3 32 66 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 66 163 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 66 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 66 163 (Polychromatic418967fa.accept_21_9_3_16_1_1684
  30 66 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 66 163 (accept_3_3 29
  66 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 66 163
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 66 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 66 163 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 66 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 66 163 (accept_3_3 26 66 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 66 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 66 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 66 163 (Polychromatic418967fa.accept_9_6_3_1_1_155 24
  66 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 66 163 (accept_3_3 23 66
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 66 163 (Polychromatic418967fa.accept_7_1_3_2_1_13
  22 66 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 66 163
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 66 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 66 163 (accept_3_3 20 66 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  66 163 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 66 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 66 163 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 66 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 66 163 (accept_3_3 17 66 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 66 163 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 66 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 66 163
  (Polychromatic418967fa.accept_7_1_3_2_1_13 15 66 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 66 163 (accept_3_3 14 66 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  66 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 66 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 66 163 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 66 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 66 163 (accept_3_3 11 66 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 66 163 (Polychromatic418967fa.accept_21_10_3_16_1_5909 10 66 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 66 163
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 66 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 66 163 (accept_3_3 8 66 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66
  163 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 66 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 66 163 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 66 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 66 163 (accept_3_3 5 66 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 66 163 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 66 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 66 163 (Polychromatic418967fa.accept_13_3_1_7_1_1706 3
  66 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 66 163 (accept_3_3 2 66 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 66
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  163)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 163 (allA_of_3_1 65 65 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 64 163 (allA_succ_of_accept 63 64 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 64 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 64 163 (accept_3_3 62 64 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  64 163 (Polychromatic418967fa.accept_19_4_7_11_1_6056 61 64 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 64 163 (Polychromatic418967fa.accept_13_8_12_7_1_2442 60 64 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 64 163 (accept_3_3 59 64 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 64 163 (Polychromatic418967fa.accept_12_10_4_7_1_948 58 64 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 64 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 64 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 64 163 (accept_3_3 56 64 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  64 163 (Polychromatic418967fa.accept_7_6_1_2_1_230 55 64 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 64 163 (Polychromatic418967fa.accept_15_9_4_13_1_4482 54 64 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 64 163 (accept_3_3 53 64 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 64 163 (Polychromatic418967fa.accept_7_3_1_2_1_247 52 64 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 64 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 64 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 64 163 (accept_3_3 50 64 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  64 163 (Polychromatic418967fa.accept_10_9_4_3_1_539 49 64 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 64 163 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 64 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 64 163 (accept_3_3 47 64 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 64 163 (Polychromatic418967fa.accept_12_10_4_7_1_948 46 64 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 64 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 64 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 64 163 (accept_3_3 44 64 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  64 163 (Polychromatic418967fa.accept_13_4_12_7_1_2439 43 64 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 64 163 (Polychromatic418967fa.accept_19_4_7_11_1_6056 42 64 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 64 163 (accept_3_3 41 64 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 64 163 (Polychromatic418967fa.accept_15_10_4_13_1_4506 40 64
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 64 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 64 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 64 163 (accept_3_3 38 64 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  64 163 (Polychromatic418967fa.accept_10_7_4_3_1_560 37 64 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 64 163 (Polychromatic418967fa.accept_13_10_12_7_1_1079 36 64 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 64 163 (accept_3_3 35 64 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 64 163 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 64 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 64 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 64 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 64 163 (accept_3_3 32 64 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  64 163 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 64 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 64 163 (Polychromatic418967fa.accept_13_4_12_7_1_2439 30 64 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 64 163 (accept_3_3 29 64 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 64 163 (Polychromatic418967fa.accept_19_9_7_11_1_7602 28 64
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 64 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 64 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 64 163 (accept_3_3 26 64 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  64 163 (Polychromatic418967fa.accept_15_10_4_13_1_4506 25 64 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 64 163 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 64 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 64 163 (accept_3_3 23 64 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 64 163 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 64 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 64 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 64 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 64 163 (accept_3_3 20 64 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  64 163 (Polychromatic418967fa.accept_10_9_4_3_1_539 19 64 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 64 163 (Polychromatic418967fa.accept_13_5_12_7_1_1080 18 64 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 64 163 (accept_3_3 17 64 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 64 163 (Polychromatic418967fa.accept_18_16_10_1_1_3696 16 64
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 64 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 64 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 64 163 (accept_3_3 14 64 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  64 163 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 64 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 64 163 (Polychromatic418967fa.accept_19_12_7_11_1_7658 12 64 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 64 163 (accept_3_3 11 64 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 64 163 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 64 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 64 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 64 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 64 163 (accept_3_3 8 64 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 64
  163 (Polychromatic418967fa.accept_10_7_4_3_1_560 7 64 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 64 163 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 64 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 64 163 (accept_3_3 5 64 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 64 163 (Polychromatic418967fa.accept_13_4_12_7_1_2439 4 64 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 64 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 64
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 64 163 (accept_3_3 2 64 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 64 163 (Polychromatic418967fa.accept_14_1_8_9_1_1312 1
  64 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64
  163)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 163 (allA_succ_of_accept 62 63 163
  (accept_3_3 62 63 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 63 163
  (Polychromatic418967fa.accept_13_9_11_7_1_1077 61 63 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 63 163 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 63 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 63 163 (accept_3_3 59 63 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 63 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 63 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 163 (Polychromatic418967fa.accept_12_9_3_7_1_924
  57 63 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 163 (accept_3_3 56
  63 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 63 163
  (Polychromatic418967fa.accept_13_3_11_7_1_2488 55 63 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 63 163 (Polychromatic418967fa.accept_11_10_8_9_1_492 54 63 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 63 163 (accept_3_3 53 63 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 63 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 63 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 163
  (Polychromatic418967fa.accept_13_12_11_7_1_2491 51 63 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 63 163 (accept_3_3 50 63 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  63 163 (Polychromatic418967fa.accept_27_22_9_1_1_9048 49 63 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 63 163 (Polychromatic418967fa.accept_13_9_11_7_1_1077 48 63 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 63 163 (accept_3_3 47 63 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 63 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 163
  (Polychromatic418967fa.accept_12_9_3_7_1_924 45 63 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 63 163 (accept_3_3 44 63 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  63 163 (Polychromatic418967fa.accept_11_10_8_9_1_492 43 63 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 63 163 (Polychromatic418967fa.accept_13_3_11_7_1_2488 42 63 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 63 163 (accept_3_3 41 63 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 63 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 163
  (Polychromatic418967fa.accept_15_9_3_13_1_1686 39 63 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 63 163 (accept_3_3 38 63 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  63 163 (Polychromatic418967fa.accept_19_18_6_11_1_7696 37 63 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 63 163 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 63 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 63 163 (accept_3_3 35 63 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 63 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 163
  (Polychromatic418967fa.accept_12_9_3_7_1_924 33 63 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 63 163 (accept_3_3 32 63 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  63 163 (Polychromatic418967fa.accept_13_5_11_7_1_559 31 63 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 63 163 (Polychromatic418967fa.accept_13_4_11_7_1_558 30 63 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 163 (accept_3_3 29 63 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 63 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 163
  (Polychromatic418967fa.accept_13_1_11_7_1_1704 27 63 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 63 163 (accept_3_3 26 63 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  63 163 (Polychromatic418967fa.accept_13_12_11_7_1_2491 25 63 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 63 163 (Polychromatic418967fa.accept_15_9_3_13_1_1686 24 63 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 163 (accept_3_3 23 63 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 63 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 163
  (Polychromatic418967fa.accept_11_10_8_9_1_492 21 63 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 63 163 (accept_3_3 20 63 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  63 163 (Polychromatic418967fa.accept_14_5_7_9_1_3828 19 63 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 63 163 (Polychromatic418967fa.accept_13_5_11_7_1_559 18 63 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 163 (accept_3_3 17 63 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 63 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 163
  (Polychromatic418967fa.accept_19_15_6_11_1_9047 15 63 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 63 163 (accept_3_3 14 63 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  63 163 (Polychromatic418967fa.accept_16_13_15_3_1_4196 13 63 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 63 163 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 63 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 163 (accept_3_3 11 63 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 63 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 163
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 63 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 63 163 (accept_3_3 8 63 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63
  163 (Polychromatic418967fa.accept_16_7_15_3_1_1302 7 63 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 63 163 (Polychromatic418967fa.accept_17_6_12_10_1_7781 6 63 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 163 (accept_3_3 5 63 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 63 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 163
  (Polychromatic418967fa.accept_13_3_11_7_1_2488 3 63 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 63 163 (accept_3_3 2 63 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63
  163 (Polychromatic418967fa.accept_13_1_11_7_1_1704 1 63 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 63 163))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 163
  (allA_of_3_1 62 62 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 61 163 (allA_succ_of_accept 60 61 163
  (Polychromatic418967fa.accept_7_4_5_2_1_243 60 61 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 163 (accept_3_3 59 61 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 61 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 163 (Polychromatic418967fa.accept_9_3_7_1_1_143 57 61 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 163 (accept_3_3 56 61 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 163 (Polychromatic418967fa.accept_13_3_9_7_1_1730 55 61 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 163
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 61 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 163 (accept_3_3 53 61 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 163 (Polychromatic418967fa.accept_7_3_5_2_1_17 52 61 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 163 (Polychromatic418967fa.accept_9_6_7_1_1_145 51 61 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 163 (accept_3_3 50 61 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 163 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 61 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 163
  (Polychromatic418967fa.accept_9_3_7_1_1_143 48 61 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 163 (accept_3_3 47 61 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 61 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 163 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 61 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 163 (accept_3_3 44 61 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 163 (Polychromatic418967fa.accept_13_4_9_7_1_2402 43 61 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 163
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 61 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 163 (accept_3_3 41 61 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 163 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 61 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 163 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 61 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 163 (accept_3_3 38 61 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 163 (Polychromatic418967fa.accept_13_11_9_7_1_2484 37 61 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 163
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 61 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 163 (accept_3_3 35 61 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 61 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 163 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 61 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 163 (accept_3_3 32 61 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 163 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 61 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 163
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 61 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 163 (accept_3_3 29 61 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 163 (Polychromatic418967fa.accept_10_8_1_3_1_1374 28 61 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 163 (Polychromatic418967fa.accept_15_12_1_13_1_3444 27 61 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 163 (accept_3_3 26 61 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 163 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 61 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 163
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 61 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 163 (accept_3_3 23 61 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 61 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 163 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 61 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 163 (accept_3_3 20 61 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 163 (Polychromatic418967fa.accept_13_6_9_7_1_2430 19 61 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 163
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 61 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 163 (accept_3_3 17 61 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 163 (Polychromatic418967fa.accept_13_3_9_7_1_1730 16 61 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 163 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 61 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 163 (accept_3_3 14 61 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 163 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 61 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 163
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 61 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 163 (accept_3_3 11 61 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 61 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 163 (Polychromatic418967fa.accept_29_9_3_18_1_9046 9 61 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 163 (accept_3_3 8 61 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 163 (Polychromatic418967fa.accept_14_7_5_9_1_2911 7 61 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 163
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 61 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 163 (accept_3_3 5 61 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  163 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 61 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 163 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 61 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 163 (accept_3_3 2 61 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 163 (Polychromatic418967fa.accept_16_1_13_3_1_2168 1 61 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 163)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 163 (allA_succ_of_accept 59 60 163 (accept_3_3 59 60 163 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 60 163 (Polychromatic418967fa.accept_9_4_6_1_1_393 58 60 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 60 163 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 60 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 60 163 (accept_3_3 56 60 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 60 163 (Polychromatic418967fa.accept_7_6_4_2_1_236 55
  60 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 60 163
  (Polychromatic418967fa.accept_7_5_4_2_1_235 54 60 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 60 163 (accept_3_3 53 60 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  60 163 (Polychromatic418967fa.accept_9_7_6_1_1_709 52 60 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 60 163 (Polychromatic418967fa.accept_11_7_5_9_1_884 51 60 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 60 163 (accept_3_3 50 60 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 60 163 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 60 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 60 163
  (Polychromatic418967fa.accept_7_6_4_2_1_236 48 60 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 60 163 (accept_3_3 47 60 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  60 163 (Polychromatic418967fa.accept_19_8_3_11_1_6048 46 60 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 60 163 (Polychromatic418967fa.accept_18_9_6_1_1_3687 45 60 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 60 163 (accept_3_3 44 60 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 163 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 60 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 60 163
  (Polychromatic418967fa.accept_13_3_8_7_1_4135 42 60 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 60 163 (accept_3_3 41 60 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  60 163 (Polychromatic418967fa.accept_7_5_4_2_1_235 40 60 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 60 163 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 60 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 60 163 (accept_3_3 38 60 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 163 (Polychromatic418967fa.accept_17_3_9_10_1_9045 37 60 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 60 163
  (Polychromatic418967fa.accept_13_10_8_7_1_1074 36 60 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 60 163 (accept_3_3 35 60 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  60 163 (Polychromatic418967fa.accept_7_6_4_2_1_236 34 60 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 60 163 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 60 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 60 163 (accept_3_3 32 60 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 163 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 60 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 60 163
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 60 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 60 163 (accept_3_3 29 60 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  60 163 (Polychromatic418967fa.accept_13_2_8_7_1_2424 28 60 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 60 163 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 60 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 60 163 (accept_3_3 26 60 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 60 163 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 60 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 60 163
  (Polychromatic418967fa.accept_16_8_12_3_1_4194 24 60 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 60 163 (accept_3_3 23 60 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  60 163 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 60 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 60 163 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 60 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 60 163 (accept_3_3 20 60 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 163 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 60 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 60 163
  (Polychromatic418967fa.accept_11_7_5_9_1_884 18 60 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 60 163 (accept_3_3 17 60 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  60 163 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 60 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 60 163 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 60 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 60 163 (accept_3_3 14 60 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 163 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 60 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 60 163
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 60 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 60 163 (accept_3_3 11 60 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  60 163 (Polychromatic418967fa.accept_13_10_8_7_1_1074 10 60 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 60 163 (Polychromatic418967fa.accept_13_9_8_7_1_1073 9 60 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 60 163 (accept_3_3 8 60 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 163 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 60 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 60 163
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 60 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 60 163 (accept_3_3 5 60 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 60
  163 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 60 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 60 163 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 60 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 60 163 (accept_3_3 2 60 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 60 163 (Polychromatic418967fa.accept_13_1_8_7_1_1088 1 60 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60 163))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 59 163 (allA_of_3_1 59 59 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 58 163
  (allA_succ_of_accept 57 58 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 58 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 58 163 (accept_3_3 56 58 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 58 163 (Polychromatic418967fa.accept_10_5_8_3_1_229 55 58 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 58 163 (Polychromatic418967fa.accept_17_3_7_10_1_3948
  54 58 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 58 163 (accept_3_3 53
  58 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 58 163
  (Polychromatic418967fa.accept_9_7_4_1_1_391 52 58 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 58 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 58 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 58 163 (accept_3_3 50 58 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 58 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 58 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 58 163 (Polychromatic418967fa.accept_9_3_4_1_1_22 48
  58 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 58 163 (accept_3_3 47 58
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 58 163
  (Polychromatic418967fa.accept_10_6_8_3_1_930 46 58 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 58 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 58 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 58 163 (accept_3_3 44 58 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 58 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 58 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 58 163 (Polychromatic418967fa.accept_9_6_4_1_1_390 42
  58 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 58 163 (accept_3_3 41 58
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 58 163
  (Polychromatic418967fa.accept_12_4_10_7_1_149 40 58 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 58 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 58 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 58 163 (accept_3_3 38 58 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 58 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 58 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 58 163 (Polychromatic418967fa.accept_10_6_8_3_1_930
  36 58 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 58 163 (accept_3_3 35
  58 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 58 163
  (Polychromatic418967fa.accept_9_7_4_1_1_391 34 58 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 58 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 58 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 58 163 (accept_3_3 32 58 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 58 163 (Polychromatic418967fa.accept_10_1_8_3_1_947 31 58 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 58 163 (Polychromatic418967fa.accept_9_3_4_1_1_22 30
  58 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 58 163 (accept_3_3 29 58
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 58 163
  (Polychromatic418967fa.accept_11_6_3_9_1_906 28 58 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 58 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 58 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 58 163 (accept_3_3 26 58 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 58 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 58 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 58 163 (Polychromatic418967fa.accept_9_6_4_1_1_390 24
  58 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 58 163 (accept_3_3 23 58
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 58 163
  (Polychromatic418967fa.accept_13_9_6_7_1_551 22 58 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 58 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 58 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 58 163 (accept_3_3 20 58 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 58 163 (Polychromatic418967fa.accept_22_19_14_9_1_7261 19 58 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 58 163
  (Polychromatic418967fa.accept_14_4_2_9_1_2092 18 58 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 58 163 (accept_3_3 17 58 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  58 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 58 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 58 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 58 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 58 163 (accept_3_3 14 58 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 58 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 58 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 58 163
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 58 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 58 163 (accept_3_3 11 58 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  58 163 (Polychromatic418967fa.accept_19_10_1_11_1_7532 10 58 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 58 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 58 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 58 163 (accept_3_3 8 58 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 58 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 58 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 58 163
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 58 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 58 163 (accept_3_3 5 58 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 58
  163 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 58 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 58 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 58 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 58 163 (accept_3_3 2 58 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 58 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 58 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  163)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 163 (allA_succ_of_accept 56 57 163
  (accept_3_3 56 57 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 163
  (Polychromatic418967fa.accept_7_6_1_2_1_230 55 57 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 57 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 57 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 163 (accept_3_3 53 57 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 57 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 57 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 163 (Polychromatic418967fa.accept_9_6_3_1_1_155 51
  57 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 163 (accept_3_3 50 57
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 163
  (Polychromatic418967fa.accept_9_4_3_1_1_154 49 57 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 57 163 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 57 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 57 163 (accept_3_3 47 57 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 57 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 57 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 163 (Polychromatic418967fa.accept_7_3_1_2_1_247 45
  57 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 163 (accept_3_3 44 57
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 163
  (Polychromatic418967fa.accept_9_7_3_1_1_386 43 57 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 57 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 57 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 57 163 (accept_3_3 41 57 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 57 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 57 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 163 (Polychromatic418967fa.accept_12_3_9_7_1_472
  39 57 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 163 (accept_3_3 38
  57 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 163
  (Polychromatic418967fa.accept_11_4_2_9_1_496 37 57 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 57 163 (Polychromatic418967fa.accept_10_6_7_3_1_547 36 57 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 57 163 (accept_3_3 35 57 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 57 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 57 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 163 (Polychromatic418967fa.accept_9_6_3_1_1_155 33
  57 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 163 (accept_3_3 32 57
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 163
  (Polychromatic418967fa.accept_7_3_1_2_1_247 31 57 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 57 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 57 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 57 163 (accept_3_3 29 57 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 57 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 57 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 163 (Polychromatic418967fa.accept_7_6_1_2_1_230 27
  57 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 163 (accept_3_3 26 57
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 163
  (Polychromatic418967fa.accept_9_7_3_1_1_386 25 57 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 57 163 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 57 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 57 163 (accept_3_3 23 57 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 57 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 57 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 163 (Polychromatic418967fa.accept_17_4_6_10_1_5164
  21 57 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 163 (accept_3_3 20
  57 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 163
  (Polychromatic418967fa.accept_25_19_7_13_1_9044 19 57 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 57 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 57 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 57 163 (accept_3_3 17 57 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 57 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 57 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 163 (Polychromatic418967fa.accept_9_6_3_1_1_155 15
  57 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 163 (accept_3_3 14 57
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 163
  (Polychromatic418967fa.accept_7_6_1_2_1_230 13 57 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 57 163 (Polychromatic418967fa.accept_13_12_5_7_1_1696 12 57 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 57 163 (accept_3_3 11 57 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 57 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 57 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 163 (Polychromatic418967fa.accept_18_9_3_1_1_2559 9
  57 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 163 (accept_3_3 8 57 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 163 (Polychromatic418967fa.accept_9_7_3_1_1_386 7
  57 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 163
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 57 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 163 (accept_3_3 5 57 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57
  163 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 57 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 57 163 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 57 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 163 (accept_3_3 2 57 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 57 163 (Polychromatic418967fa.accept_15_1_12_13_1_944 1 57 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 163)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 163 (allA_of_3_1 56 56 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 55 163
  (allA_succ_of_accept 54 55 163 (Polychromatic418967fa.accept_40_14_15_3_1_9043 54 55 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 163 (accept_3_3 53 55 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 55 163 (Polychromatic418967fa.accept_7_3_6_2_1_90 52 55 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 163
  (Polychromatic418967fa.accept_19_13_17_11_1_4716 51 55 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 55 163 (accept_3_3 50 55 163 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 55 163 (Polychromatic418967fa.accept_13_10_3_7_1_2517 49 55 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 55 163 (Polychromatic418967fa.accept_10_8_5_3_1_543 48 55 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 163 (accept_3_3 47 55 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 55 163 (Polychromatic418967fa.accept_7_4_6_2_1_451 46
  55 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 55 163
  (Polychromatic418967fa.accept_7_3_6_2_1_90 45 55 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 55 163 (accept_3_3 44 55 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  55 163 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 55 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 55 163 (Polychromatic418967fa.accept_10_2_5_3_1_1408 42 55 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 55 163 (accept_3_3 41 55 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 55 163 (Polychromatic418967fa.accept_13_1_3_7_1_1710 40 55 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 55 163
  (Polychromatic418967fa.accept_7_4_6_2_1_451 39 55 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 55 163 (accept_3_3 38 55 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  55 163 (Polychromatic418967fa.accept_10_7_5_3_1_542 37 55 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 55 163 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 55 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 55 163 (accept_3_3 35 55 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 55 163 (Polychromatic418967fa.accept_13_8_3_7_1_2455 34 55 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 55 163
  (Polychromatic418967fa.accept_15_3_10_13_1_2605 33 55 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 55 163 (accept_3_3 32 55 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  55 163 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 55 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 55 163 (Polychromatic418967fa.accept_13_4_3_7_1_2515 30 55 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 55 163 (accept_3_3 29 55 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 163 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 55 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 163
  (Polychromatic418967fa.accept_10_7_5_3_1_542 27 55 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 55 163 (accept_3_3 26 55 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  55 163 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 55 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 55 163 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 55 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 55 163 (accept_3_3 23 55 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 55 163 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 55 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 163
  (Polychromatic418967fa.accept_13_8_3_7_1_2455 21 55 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 55 163 (accept_3_3 20 55 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  55 163 (Polychromatic418967fa.accept_15_4_10_13_1_2565 19 55 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 55 163 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 55 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 163 (accept_3_3 17 55 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 55 163 (Polychromatic418967fa.accept_15_1_10_13_1_939 16 55 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 55 163
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 55 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 55 163 (accept_3_3 14 55 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  55 163 (Polychromatic418967fa.accept_19_13_17_11_1_4716 13 55 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 55 163 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 55 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 55 163 (accept_3_3 11 55 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 55 163 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 55 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 55 163
  (Polychromatic418967fa.accept_13_9_3_7_1_1065 9 55 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 55 163 (accept_3_3 8 55 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55
  163 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 55 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 55 163 (Polychromatic418967fa.accept_17_6_4_10_1_5176 6 55 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 55 163 (accept_3_3 5 55 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 55 163 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 55 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 163 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 55
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 163 (accept_3_3 2 55 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55 163 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 55
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55
  163))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 54 163 (allA_succ_of_accept 53 54 163
  (accept_3_3 53 54 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 54 163
  (Polychromatic418967fa.accept_7_3_5_2_1_17 52 54 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 54 163 (Polychromatic418967fa.accept_19_13_16_11_1_6047 51 54 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 54 163 (accept_3_3 50 54 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 54 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 54 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 163 (Polychromatic418967fa.accept_13_9_2_7_1_1083
  48 54 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 54 163 (accept_3_3 47
  54 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 54 163
  (Polychromatic418967fa.accept_7_4_5_2_1_243 46 54 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 54 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 54 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 54 163 (accept_3_3 44 54 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 54 163 (Polychromatic418967fa.accept_16_11_6_3_1_6564 43 54 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 163
  (Polychromatic418967fa.accept_19_4_16_11_1_6046 42 54 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 54 163 (accept_3_3 41 54 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  54 163 (Polychromatic418967fa.accept_19_2_16_11_1_6045 40 54 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 54 163 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 54 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 54 163 (accept_3_3 38 54 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 54 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 54 163
  (Polychromatic418967fa.accept_16_4_6_3_1_1311 36 54 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 54 163 (accept_3_3 35 54 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  54 163 (Polychromatic418967fa.accept_11_1_10_9_1_871 34 54 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 54 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 54 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 54 163 (accept_3_3 32 54 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 163 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 54 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 54 163
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 30 54 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 54 163 (accept_3_3 29 54 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  54 163 (Polychromatic418967fa.accept_17_11_3_10_1_2838 28 54 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 54 163 (Polychromatic418967fa.accept_10_7_4_3_1_560 27 54 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 163 (accept_3_3 26 54 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 54 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 54 163
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 54 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 54 163 (accept_3_3 23 54 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  54 163 (Polychromatic418967fa.accept_13_9_2_7_1_1083 22 54 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 54 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 54 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 163 (accept_3_3 20 54 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 163 (Polychromatic418967fa.accept_10_9_4_3_1_539 19 54 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 54 163
  (Polychromatic418967fa.accept_7_4_5_2_1_243 18 54 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 54 163 (accept_3_3 17 54 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  54 163 (Polychromatic418967fa.accept_23_16_8_2_1_9042 16 54 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 54 163 (Polychromatic418967fa.accept_19_15_16_11_1_7689 15 54 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 163 (accept_3_3 14 54 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 54 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 54 163
  (Polychromatic418967fa.accept_11_1_10_9_1_871 12 54 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 54 163 (accept_3_3 11 54 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  54 163 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 54 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 54 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 54 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 163 (accept_3_3 8 54 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 163 (Polychromatic418967fa.accept_10_7_4_3_1_560 7 54 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54 163
  (Polychromatic418967fa.accept_19_6_16_11_1_9041 6 54 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 54 163 (accept_3_3 5 54 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54
  163 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 54 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 54 163 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 54 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 163 (accept_3_3 2 54 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 54 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 54 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54 163))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 53 163 (allA_of_3_1 53 53 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 52 163
  (allA_succ_of_accept 51 52 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 52 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 52 163 (accept_3_3 50 52 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 52 163 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 52 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 163 (Polychromatic418967fa.accept_7_6_3_2_1_461 48
  52 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 52 163 (accept_3_3 47 52
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 52 163
  (Polychromatic418967fa.accept_12_10_4_7_1_948 46 52 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 52 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 52 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 52 163 (accept_3_3 44 52 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 52 163 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 52 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 52 163 (Polychromatic418967fa.accept_9_6_7_1_1_145 42
  52 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 52 163 (accept_3_3 41 52
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 52 163
  (Polychromatic418967fa.accept_7_5_3_2_1_249 40 52 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 52 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 52 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 52 163 (accept_3_3 38 52 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 52 163 (Polychromatic418967fa.accept_27_10_25_1_1_9040 37 52 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 52 163
  (Polychromatic418967fa.accept_7_1_3_2_1_13 36 52 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 52 163 (accept_3_3 35 52 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  52 163 (Polychromatic418967fa.accept_7_6_3_2_1_461 34 52 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 52 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 52 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 52 163 (accept_3_3 32 52 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 52 163 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 52 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 52 163
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 52 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 52 163 (accept_3_3 29 52 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  52 163 (Polychromatic418967fa.accept_16_12_4_3_1_4295 28 52 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 52 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 52 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 52 163 (accept_3_3 26 52 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 52 163 (Polychromatic418967fa.accept_10_5_2_3_1_239 25 52 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 52 163
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 52 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 52 163 (accept_3_3 23 52 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  52 163 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 52 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 52 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 52 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 52 163 (accept_3_3 20 52 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 52 163 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 52 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 52 163
  (Polychromatic418967fa.accept_22_18_8_9_1_9039 18 52 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 52 163 (accept_3_3 17 52 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  52 163 (Polychromatic418967fa.accept_19_16_14_11_1_4711 16 52 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 52 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 52 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 52 163 (accept_3_3 14 52 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 52 163 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 52 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 52 163
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 52 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 52 163 (accept_3_3 11 52 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  52 163 (Polychromatic418967fa.accept_11_10_8_9_1_492 10 52 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 52 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 52 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 52 163 (accept_3_3 8 52 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 52 163 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 52 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 52 163
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 52 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 52 163 (accept_3_3 5 52 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 52
  163 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 52 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 52 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 52 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 52 163 (accept_3_3 2 52 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 52 163 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 52 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52 163))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 51 163 (allA_succ_of_accept 50 51 163 (accept_3_3 50 51 163 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 163 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 51 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 51 163 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 51 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 163 (accept_3_3 47 51 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 46
  51 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 163
  (Polychromatic418967fa.accept_12_9_3_7_1_924 45 51 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 51 163 (accept_3_3 44 51 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  51 163 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 51 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 51 163 (Polychromatic418967fa.accept_10_2_1_3_1_233 42 51 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 163 (accept_3_3 41 51 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 51 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 163
  (Polychromatic418967fa.accept_9_3_6_1_1_24 39 51 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 51 163 (accept_3_3 38 51 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  51 163 (Polychromatic418967fa.accept_13_11_12_7_1_2443 37 51 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 51 163 (Polychromatic418967fa.accept_13_10_12_7_1_1079 36 51 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 51 163 (accept_3_3 35 51 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 51 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 163
  (Polychromatic418967fa.accept_12_9_3_7_1_924 33 51 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 51 163 (accept_3_3 32 51 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  51 163 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 51 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 51 163 (Polychromatic418967fa.accept_9_3_6_1_1_24 30 51 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 163 (accept_3_3 29 51 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 51 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 163
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 51 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 51 163 (accept_3_3 26 51 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  51 163 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 51 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 51 163 (Polychromatic418967fa.accept_11_2_7_9_1_890 24 51 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 51 163 (accept_3_3 23 51 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 51 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 163
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 51 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 51 163 (accept_3_3 20 51 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  51 163 (Polychromatic418967fa.accept_13_6_12_7_1_5131 19 51 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 51 163 (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 51 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 51 163 (accept_3_3 17 51 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 51 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 163
  (Polychromatic418967fa.accept_21_15_9_16_1_7341 15 51 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 51 163 (accept_3_3 14 51 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  51 163 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 51 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 51 163 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 51 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 163 (accept_3_3 11 51 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 51 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 163
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 51 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 51 163 (accept_3_3 8 51 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51
  163 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 51 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 51 163 (Polychromatic418967fa.accept_13_6_12_7_1_5131 6 51 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 51 163 (accept_3_3 5 51 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 51 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 51 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 51 163 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 51
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 163 (accept_3_3 2 51 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 163 (Polychromatic418967fa.accept_24_1_3_19_1_9038
  1 51 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51
  163))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 163 (allA_of_3_1 50 50 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 49 163 (allA_succ_of_accept 48 49 163 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 49
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 163 (accept_3_3 47 49 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 49 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 46
  49 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 163
  (Polychromatic418967fa.accept_16_13_1_3_1_2205 45 49 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 49 163 (accept_3_3 44 49 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  49 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 49 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 49 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 49 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 49 163 (accept_3_3 41 49 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 49 163 (Polychromatic418967fa.accept_11_7_5_9_1_884 40 49 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 163
  (Polychromatic418967fa.accept_9_3_4_1_1_22 39 49 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 49 163 (accept_3_3 38 49 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  49 163 (Polychromatic418967fa.accept_22_15_5_9_1_9037 37 49 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 49 163 (Polychromatic418967fa.accept_10_6_9_3_1_935 36 49 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 49 163 (accept_3_3 35 49 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 49 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 49 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 163
  (Polychromatic418967fa.accept_9_6_4_1_1_390 33 49 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 49 163 (accept_3_3 32 49 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  49 163 (Polychromatic418967fa.accept_21_10_7_16_1_9036 31 49 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 49 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 49 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 163 (accept_3_3 29 49 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 49 163 (Polychromatic418967fa.accept_18_10_13_1_1_7736 28 49 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 163
  (Polychromatic418967fa.accept_21_6_7_16_1_9035 27 49 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 49 163 (accept_3_3 26 49 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  49 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 49 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 49 163 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 49 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 163 (accept_3_3 23 49 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 49 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 163
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 49 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 49 163 (accept_3_3 20 49 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  49 163 (Polychromatic418967fa.accept_14_5_7_9_1_3828 19 49 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 49 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 49 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 163 (accept_3_3 17 49 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 49 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 49 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 163
  (Polychromatic418967fa.accept_9_6_4_1_1_390 15 49 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 49 163 (accept_3_3 14 49 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  49 163 (Polychromatic418967fa.accept_16_13_1_3_1_2205 13 49 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 49 163 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 49 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 163 (accept_3_3 11 49 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 49 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 163
  (Polychromatic418967fa.accept_15_9_4_13_1_4482 9 49 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 163 (accept_3_3 8 49 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49
  163 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 49 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 49 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 49 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 163 (accept_3_3 5 49 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 49 163 (Polychromatic418967fa.accept_10_4_9_3_1_1907 4 49 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 163 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 49
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 163 (accept_3_3 2 49 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 163 (Polychromatic418967fa.accept_21_1_7_16_1_5859
  1 49 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49
  163))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 48 163 (allA_succ_of_accept 47 48 163 (accept_3_3 47
  48 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 48 163
  (Polychromatic418967fa.accept_7_4_6_2_1_451 46 48 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 48 163 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 48 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 48 163 (accept_3_3 44 48 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 48 163 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 48 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 48 163 (Polychromatic418967fa.accept_9_6_3_1_1_155 42
  48 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 48 163 (accept_3_3 41 48
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 48 163
  (Polychromatic418967fa.accept_9_4_3_1_1_154 40 48 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 48 163 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 48 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 48 163 (accept_3_3 38 48 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 48 163 (Polychromatic418967fa.accept_13_11_9_7_1_2484 37 48 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 163
  (Polychromatic418967fa.accept_7_1_6_2_1_18 36 48 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 48 163 (accept_3_3 35 48 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  48 163 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 48 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 48 163 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 48 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 48 163 (accept_3_3 32 48 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 163 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 48 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 163
  (Polychromatic418967fa.accept_13_4_9_7_1_2402 30 48 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 48 163 (accept_3_3 29 48 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  48 163 (Polychromatic418967fa.accept_13_2_9_7_1_164 28 48 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 48 163 (Polychromatic418967fa.accept_15_12_3_13_1_4481 27 48 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 48 163 (accept_3_3 26 48 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 163 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 48 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 163
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 48 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 48 163 (accept_3_3 23 48 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  48 163 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 48 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 48 163 (Polychromatic418967fa.accept_10_1_8_3_1_947 21 48 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 48 163 (accept_3_3 20 48 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 163 (Polychromatic418967fa.accept_13_6_9_7_1_2430 19 48 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 48 163
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 48 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 48 163 (accept_3_3 17 48 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  48 163 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 48 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 48 163 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 48 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 48 163 (accept_3_3 14 48 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 163 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 48 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 48 163
  (Polychromatic418967fa.accept_15_12_3_13_1_4481 12 48 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 48 163 (accept_3_3 11 48 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  48 163 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 48 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 48 163 (Polychromatic418967fa.accept_15_9_3_13_1_1686 9 48 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 48 163 (accept_3_3 8 48 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 163 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 48 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 163
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 48 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 48 163 (accept_3_3 5 48 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48
  163 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 48 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 48 163 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 48 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 48 163 (accept_3_3 2 48 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 48 163 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 48 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48 163)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  47 163 (allA_of_3_1 47 47 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 46 163 (allA_succ_of_accept 45 46
  163 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 46 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 46 163 (accept_3_3 44 46 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  46 163 (Polychromatic418967fa.accept_16_11_14_3_1_3140 43 46 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 46 163 (Polychromatic418967fa.accept_15_12_1_13_1_3444 42 46 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 163 (accept_3_3 41 46 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 46 163 (Polychromatic418967fa.accept_7_5_4_2_1_235 40 46 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 46 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 46 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 46 163 (accept_3_3 38 46 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  46 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 46 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 46 163 (Polychromatic418967fa.accept_17_2_12_10_1_9034 36 46 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 46 163 (accept_3_3 35 46 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 46 163 (Polychromatic418967fa.accept_7_6_4_2_1_236 34 46 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 46 163
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 46 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 46 163 (accept_3_3 32 46 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  46 163 (Polychromatic418967fa.accept_18_13_10_1_1_9025 31 46 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 46 163 (Polychromatic418967fa.accept_14_2_4_9_1_2121 30 46 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 46 163 (accept_3_3 29 46 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 46 163 (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 46 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 46 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 46 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 46 163 (accept_3_3 26 46 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  46 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 46 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 46 163 (Polychromatic418967fa.accept_25_24_21_13_1_9033 24 46 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 163 (accept_3_3 23 46 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 46 163 (Polychromatic418967fa.accept_17_5_12_10_1_3963 22 46
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 46 163
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 46 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 46 163 (accept_3_3 20 46 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  46 163 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 46 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 46 163 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 46 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 163 (accept_3_3 17 46 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 46 163 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 46 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 46 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 46 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 46 163 (accept_3_3 14 46 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  46 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 46 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 46 163 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 46 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 46 163 (accept_3_3 11 46 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 46 163 (Polychromatic418967fa.accept_15_10_1_13_1_2609 10 46 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 46 163
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 46 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 46 163 (accept_3_3 8 46 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 46
  163 (Polychromatic418967fa.accept_10_7_6_3_1_927 7 46 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 46 163 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 46 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 46 163 (accept_3_3 5 46 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 46 163 (Polychromatic418967fa.accept_11_4_2_9_1_496 4 46 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 46 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 46
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 46 163 (accept_3_3 2 46 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 46 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 46
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  163)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 163 (allA_succ_of_accept 44 45 163 (accept_3_3 44 45
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 163 (Polychromatic418967fa.accept_7_1_3_2_1_13
  43 45 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 45 163
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 45 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 45 163 (accept_3_3 41 45 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  45 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 45 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 45 163 (Polychromatic418967fa.accept_12_3_9_7_1_472 39 45 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 163 (accept_3_3 38 45 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 163 (Polychromatic418967fa.accept_10_7_5_3_1_542 37 45 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 163
  (Polychromatic418967fa.accept_7_1_3_2_1_13 36 45 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 45 163 (accept_3_3 35 45 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  45 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 45 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 45 163 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 45 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 163 (accept_3_3 32 45 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 163 (Polychromatic418967fa.accept_16_15_13_3_1_4215 31 45 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 45 163
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 45 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 45 163 (accept_3_3 29 45 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  45 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 45 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 45 163 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 45 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 163 (accept_3_3 26 45 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 163 (Polychromatic418967fa.accept_13_12_6_7_1_1071 25 45 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 45 163
  (Polychromatic418967fa.accept_16_8_13_3_1_4253 24 45 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 45 163 (accept_3_3 23 45 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  45 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 45 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 45 163 (Polychromatic418967fa.accept_11_10_1_9_1_2060 21 45 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 163 (accept_3_3 20 45 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 163 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 45 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 45 163
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 45 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 45 163 (accept_3_3 17 45 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  45 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 45 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 45 163 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 45 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 163 (accept_3_3 14 45 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 163 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 45 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 45 163
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 45 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 45 163 (accept_3_3 11 45 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  45 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 45 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 45 163 (Polychromatic418967fa.accept_13_9_6_7_1_551 9 45 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 163 (accept_3_3 8 45 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 163 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 45 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 163
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 45 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 163 (accept_3_3 5 45 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45
  163 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 45 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 45 163 (Polychromatic418967fa.accept_12_3_9_7_1_472 3 45 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 163 (accept_3_3 2 45 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 45 163 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 45 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 163))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  163 (allA_of_3_1 44 44 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 43 163 (allA_succ_of_accept 42 43 163
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 43 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 163 (accept_3_3 41 43 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 163 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 43 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 163 (Polychromatic418967fa.accept_9_3_7_1_1_143 39 43 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 163 (accept_3_3 38 43 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 163 (Polychromatic418967fa.accept_13_11_4_7_1_2419 37 43 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 163
  (Polychromatic418967fa.accept_13_10_4_7_1_2465 36 43 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 163 (accept_3_3 35 43 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 163 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 43 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 163 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 43 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 163 (accept_3_3 32 43 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 163 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 43 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 163
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 43 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 163 (accept_3_3 29 43 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 163 (Polychromatic418967fa.accept_21_7_1_16_1_9032 28 43 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 163 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 43 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 163 (accept_3_3 26 43 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 163 (Polychromatic418967fa.accept_13_12_4_7_1_2520 25 43 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 163
  (Polychromatic418967fa.accept_7_3_1_2_1_247 24 43 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 163 (accept_3_3 23 43 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 163 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 43 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 163 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 43 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 163 (accept_3_3 20 43 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 163 (Polychromatic418967fa.accept_11_8_10_9_1_1401 19 43 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 163
  (Polychromatic418967fa.accept_17_1_9_10_1_1864 18 43 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 163 (accept_3_3 17 43 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 163 (Polychromatic418967fa.accept_13_3_4_7_1_1711 16 43 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 163 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 43 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 163 (accept_3_3 14 43 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 163 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 43 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 163
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 43 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 163 (accept_3_3 11 43 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 163 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 43 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 163 (Polychromatic418967fa.accept_13_9_4_7_1_1694 9 43 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 163 (accept_3_3 8 43 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 163 (Polychromatic418967fa.accept_16_7_11_3_1_1330 7 43 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 163
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 43 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 163 (accept_3_3 5 43 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  163 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 43 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 163 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 43 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 163 (accept_3_3 2 43 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 163 (Polychromatic418967fa.accept_11_1_10_9_1_871 1 43 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 163))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 163
  (allA_succ_of_accept 41 42 163 (accept_3_3 41 42 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  42 163 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 42 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 42 163 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 42 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 42 163 (accept_3_3 38 42 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 42 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 163
  (Polychromatic418967fa.accept_13_10_3_7_1_2517 36 42 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 42 163 (accept_3_3 35 42 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  42 163 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 42 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 42 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 42 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 42 163 (accept_3_3 32 42 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 163 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 42 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 42 163
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 42 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 42 163 (accept_3_3 29 42 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  42 163 (Polychromatic418967fa.accept_16_12_10_3_1_4209 28 42 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 42 163 (Polychromatic418967fa.accept_13_1_3_7_1_1710 27 42 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 42 163 (accept_3_3 26 42 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 42 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 163
  (Polychromatic418967fa.accept_13_11_3_7_1_2513 24 42 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 42 163 (accept_3_3 23 42 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  42 163 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 42 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 42 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 42 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 42 163 (accept_3_3 20 42 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 163 (Polychromatic418967fa.accept_17_2_8_10_1_2870 19 42 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 42 163
  (Polychromatic418967fa.accept_15_3_12_13_1_2549 18 42 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 42 163 (accept_3_3 17 42 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  42 163 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 42 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 42 163 (Polychromatic418967fa.accept_10_5_2_3_1_239 15 42 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 42 163 (accept_3_3 14 42 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 42 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 163
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 42 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 42 163 (accept_3_3 11 42 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  42 163 (Polychromatic418967fa.accept_13_10_3_7_1_2517 10 42 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 42 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 42 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 42 163 (accept_3_3 8 42 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 163 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 42 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 42 163
  (Polychromatic418967fa.accept_22_6_20_9_1_9031 6 42 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 42 163 (accept_3_3 5 42 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42
  163 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 42 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 42 163 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 42 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 42 163 (accept_3_3 2 42 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 42 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 42 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42 163)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 163
  (allA_of_3_1 41 41 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 40 163 (allA_succ_of_accept 39 40 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 40 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 40 163 (accept_3_3 38 40 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  40 163 (Polychromatic418967fa.accept_13_11_1_7_1_1691 37 40 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 40 163 (Polychromatic418967fa.accept_16_4_8_3_1_4206 36 40 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 40 163 (accept_3_3 35 40 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 40 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 40 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 40 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 40 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 40 163 (accept_3_3 32 40 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  40 163 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 40 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 40 163 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 40 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 40 163 (accept_3_3 29 40 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 40 163 (Polychromatic418967fa.accept_16_12_8_3_1_4241 28 40 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 40 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 40 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 40 163 (accept_3_3 26 40 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  40 163 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 40 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 40 163 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 40 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 40 163 (accept_3_3 23 40 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 40 163 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 40 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 40 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 40 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 40 163 (accept_3_3 20 40 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  40 163 (Polychromatic418967fa.accept_13_6_1_7_1_1690 19 40 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 40 163 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 40 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 40 163 (accept_3_3 17 40 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 40 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 40 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 40 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 40 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 40 163 (accept_3_3 14 40 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  40 163 (Polychromatic418967fa.accept_11_2_7_9_1_890 13 40 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 40 163 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 40 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 40 163 (accept_3_3 11 40 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 40 163 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 40 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 40 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 40 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 40 163 (accept_3_3 8 40 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 40
  163 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 40 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 40 163 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 40 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 40 163 (accept_3_3 5 40 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 40 163 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 40 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 40
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 40 163 (accept_3_3 2 40 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40 163 (Polychromatic418967fa.accept_15_1_10_13_1_939
  1 40 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40
  163)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 163 (allA_succ_of_accept 38 39 163 (accept_3_3 38 39 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 163 (Polychromatic418967fa.accept_15_7_9_13_1_3451
  37 39 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 39 163
  (Polychromatic418967fa.accept_8_4_7_3_1_144 36 39 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 39 163 (accept_3_3 35 39 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  39 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 39 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 39 163 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 39 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 163 (accept_3_3 32 39 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 163 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 39 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 39 163
  (Polychromatic418967fa.accept_14_2_11_9_1_2925 30 39 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 39 163 (accept_3_3 29 39 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  39 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 39 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 39 163 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 39 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 163 (accept_3_3 26 39 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 163 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 39 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 39 163
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 39 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 39 163 (accept_3_3 23 39 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  39 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 39 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 39 163 (Polychromatic418967fa.accept_12_9_3_7_1_924 21 39 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 163 (accept_3_3 20 39 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 163 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 39 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 39 163
  (Polychromatic418967fa.accept_15_3_9_13_1_1681 18 39 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 39 163 (accept_3_3 17 39 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  39 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 39 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 39 163 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 39 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 163 (accept_3_3 14 39 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 163 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 39 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 39 163
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 39 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 39 163 (accept_3_3 11 39 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  39 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 39 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 39 163 (Polychromatic418967fa.accept_12_9_3_7_1_924 9 39 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 163 (accept_3_3 8 39 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 163 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 39 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39 163
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 39 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 163 (accept_3_3 5 39 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39
  163 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 39 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 39 163 (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 39 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 163 (accept_3_3 2 39 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 39 163 (Polychromatic418967fa.accept_23_1_16_2_1_5568 1 39 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 163))))))))))))))))))))))))))))))))))))))) (allB_succ 38 163
  (allA_of_3_1 38 38 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 37 163 (allA_succ_of_accept 36 37 163
  (Polychromatic418967fa.accept_10_6_7_3_1_547 36 37 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 37 163 (accept_3_3 35 37 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  37 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 37 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 37 163 (Polychromatic418967fa.accept_25_8_12_13_1_9030 33 37 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 163 (accept_3_3 32 37 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 163 (Polychromatic418967fa.accept_13_5_11_7_1_559 31 37 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 163
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 37 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 163 (accept_3_3 29 37 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  37 163 (Polychromatic418967fa.accept_17_11_3_10_1_2838 28 37 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 163 (Polychromatic418967fa.accept_13_1_11_7_1_1704 27 37 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 163 (accept_3_3 26 37 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 163 (Polychromatic418967fa.accept_10_5_7_3_1_561 25 37 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 163
  (Polychromatic418967fa.accept_10_4_7_3_1_54 24 37 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 163 (accept_3_3 23 37 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 37 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 163 (Polychromatic418967fa.accept_15_6_7_13_1_1666 21 37 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 163 (accept_3_3 20 37 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 163 (Polychromatic418967fa.accept_26_19_11_7_1_9029 19 37
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 163
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 37 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 163 (accept_3_3 17 37 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  37 163 (Polychromatic418967fa.accept_10_6_7_3_1_547 16 37 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 163 (Polychromatic418967fa.accept_10_5_7_3_1_561 15 37 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 163 (accept_3_3 14 37 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 163 (Polychromatic418967fa.accept_11_2_4_9_1_484 13 37 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 163
  (Polychromatic418967fa.accept_13_12_11_7_1_2491 12 37 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 163 (accept_3_3 11 37 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  37 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 37 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 163 (Polychromatic418967fa.accept_13_9_11_7_1_1077 9 37 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 163 (accept_3_3 8 37 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 163 (Polychromatic418967fa.accept_17_7_3_10_1_2881 7 37 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 163
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 37 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 163 (accept_3_3 5 37 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  163 (Polychromatic418967fa.accept_10_4_7_3_1_54 4 37 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 163 (Polychromatic418967fa.accept_13_3_11_7_1_2488 3 37 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 163 (accept_3_3 2 37 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 163 (Polychromatic418967fa.accept_13_1_11_7_1_1704 1 37 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 163))))))))))))))))))))))))))))))))))))) (allB_succ 36 163
  (allA_succ_of_accept 35 36 163 (accept_3_3 35 36 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  36 163 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 36 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 36 163 (Polychromatic418967fa.accept_16_1_4_3_1_3148 33 36 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 36 163 (accept_3_3 32 36 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 163 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 36 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 36 163
  (Polychromatic418967fa.accept_13_4_10_7_1_1701 30 36 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 36 163 (accept_3_3 29 36 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  36 163 (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 36 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 36 163 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 36 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 36 163 (accept_3_3 26 36 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 163 (Polychromatic418967fa.accept_13_12_10_7_1_2433 25 36 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 36 163
  (Polychromatic418967fa.accept_7_3_1_2_1_247 24 36 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 36 163 (accept_3_3 23 36 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  36 163 (Polychromatic418967fa.accept_15_7_6_13_1_936 22 36 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 36 163 (Polychromatic418967fa.accept_13_8_10_7_1_1702 21 36 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 36 163 (accept_3_3 20 36 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 163 (Polychromatic418967fa.accept_10_9_6_3_1_545 19 36 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 163
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 36 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 36 163 (accept_3_3 17 36 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  36 163 (Polychromatic418967fa.accept_13_3_10_7_1_1061 16 36 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 36 163 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 36 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 36 163 (accept_3_3 14 36 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 163 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 36 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 36 163
  (Polychromatic418967fa.accept_13_12_10_7_1_2433 12 36 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 36 163 (accept_3_3 11 36 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  36 163 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 36 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 36 163 (Polychromatic418967fa.accept_10_9_6_3_1_545 9 36 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 36 163 (accept_3_3 8 36 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 163 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 36 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 36 163
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 36 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 36 163 (accept_3_3 5 36 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 36
  163 (Polychromatic418967fa.accept_13_4_10_7_1_1701 4 36 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 36 163 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 36 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 36 163 (accept_3_3 2 36 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 163 (Polychromatic418967fa.accept_14_1_8_9_1_1312 1 36 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 163)))))))))))))))))))))))))))))))))))) (allB_succ 35
  163 (allA_of_3_1 35 35 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 34 163 (allA_succ_of_accept 33 34 163
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 34 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 34 163 (accept_3_3 32 34 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  34 163 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 34 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 34 163 (Polychromatic418967fa.accept_9_3_7_1_1_143 30 34 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 163 (accept_3_3 29 34 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 34 163 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 34 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 34 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 34 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 34 163 (accept_3_3 26 34 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  34 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 34 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 34 163 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 34 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 163 (accept_3_3 23 34 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 34 163 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 34 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 34 163
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 34 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 34 163 (accept_3_3 20 34 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  34 163 (Polychromatic418967fa.accept_10_9_4_3_1_539 19 34 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 34 163 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 34 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 34 163 (accept_3_3 17 34 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 34 163 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 34 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 34 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 34 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 34 163 (accept_3_3 14 34 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  34 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 34 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 34 163 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 34 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 163 (accept_3_3 11 34 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 34 163 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 34 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 34 163
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 34 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 34 163 (accept_3_3 8 34 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 34
  163 (Polychromatic418967fa.accept_10_7_4_3_1_560 7 34 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 34 163 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 34 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 163 (accept_3_3 5 34 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 34 163 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 34 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 34
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 34 163 (accept_3_3 2 34 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 34
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 163))))))))))))))))))))))))))))))))))
  (allB_succ 33 163 (allA_succ_of_accept 32 33 163 (accept_3_3 32 33 163 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 163 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 33 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 33 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 163 (accept_3_3 29 33 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 28
  33 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 163
  (Polychromatic418967fa.accept_12_3_9_7_1_472 27 33 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 33 163 (accept_3_3 26 33 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  33 163 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 33 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 33 163 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 33 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 163 (accept_3_3 23 33 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 33 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 163
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 33 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 33 163 (accept_3_3 20 33 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  33 163 (Polychromatic418967fa.accept_22_19_11_9_1_9028 19 33 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 33 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 33 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 163 (accept_3_3 17 33 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 33 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 163
  (Polychromatic418967fa.accept_12_3_9_7_1_472 15 33 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 33 163 (accept_3_3 14 33 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  33 163 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 33 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 33 163 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 33 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 163 (accept_3_3 11 33 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 33 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 163
  (Polychromatic418967fa.accept_15_9_3_13_1_1686 9 33 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 33 163 (accept_3_3 8 33 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33
  163 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 33 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 33 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 33 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 163 (accept_3_3 5 33 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 33 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 33 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33 163 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 33
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 163 (accept_3_3 2 33 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 163 (Polychromatic418967fa.accept_15_1_3_13_1_2548
  1 33 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33
  163))))))))))))))))))))))))))))))))) (allB_succ 32 163 (allA_of_3_1 32 32 163 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 31 163 (allA_succ_of_accept 30 31 163 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 31 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 163 (accept_3_3 29 31 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 31 163 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 31 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 163
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 31 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 31 163 (accept_3_3 26 31 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  31 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 31 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 31 163 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 31 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 163 (accept_3_3 23 31 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 31 163 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 31 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 163
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 31 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 31 163 (accept_3_3 20 31 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  31 163 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 31 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 31 163 (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 31 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 31 163 (accept_3_3 17 31 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 31 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 31 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 163
  (Polychromatic418967fa.accept_7_1_3_2_1_13 15 31 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 31 163 (accept_3_3 14 31 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  31 163 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 31 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 31 163 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 31 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 31 163 (accept_3_3 11 31 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 31 163 (Polychromatic418967fa.accept_15_10_1_13_1_2609 10 31 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 31 163
  (Polychromatic418967fa.accept_21_9_10_16_1_7327 9 31 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 31 163 (accept_3_3 8 31 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 31
  163 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 31 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 31 163 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 31 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 31 163 (accept_3_3 5 31 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 31 163 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 31 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 31 163 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 31
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 163 (accept_3_3 2 31 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 163 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 31
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 163)))))))))))))))))))))))))))))))
  (allB_succ 30 163 (allA_succ_of_accept 29 30 163 (accept_3_3 29 30 163 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 30 163 (Polychromatic418967fa.accept_21_7_9_16_1_9027 28 30 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 30 163 (Polychromatic418967fa.accept_16_11_14_3_1_3140 27 30
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 30 163 (accept_3_3 26 30 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 30 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 25
  30 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 30 163
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 30 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 30 163 (accept_3_3 23 30 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  30 163 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 30 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 30 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 30 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 30 163 (accept_3_3 20 30 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 163 (Polychromatic418967fa.accept_13_6_4_7_1_2464 19 30 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 163
  (Polychromatic418967fa.accept_14_4_2_9_1_2092 18 30 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 30 163 (accept_3_3 17 30 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  30 163 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 30 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 30 163 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 30 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 30 163 (accept_3_3 14 30 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 30 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 163
  (Polychromatic418967fa.accept_13_12_4_7_1_2520 12 30 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 30 163 (accept_3_3 11 30 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  30 163 (Polychromatic418967fa.accept_11_10_8_9_1_492 10 30 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 30 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 30 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 30 163 (accept_3_3 8 30 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 163 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 30 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 30 163
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 30 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 30 163 (accept_3_3 5 30 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 30
  163 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 30 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 30 163 (Polychromatic418967fa.accept_13_3_4_7_1_1711 3 30 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 30 163 (accept_3_3 2 30 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 30 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 30 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 163)))))))))))))))))))))))))))))) (allB_succ 29 163 (allA_of_3_1
  29 29 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 28 163 (allA_succ_of_accept 27 28 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 28 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 28 163 (accept_3_3 26 28 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  28 163 (Polychromatic418967fa.accept_10_5_8_3_1_229 25 28 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 28 163 (Polychromatic418967fa.accept_16_8_12_3_1_4194 24 28 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 163 (accept_3_3 23 28 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 28 163 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 28 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 28 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 28 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 28 163 (accept_3_3 20 28 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  28 163 (Polychromatic418967fa.accept_22_19_6_9_1_9026 19 28 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 28 163 (Polychromatic418967fa.accept_13_5_2_7_1_2414 18 28 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 28 163 (accept_3_3 17 28 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 28 163 (Polychromatic418967fa.accept_10_6_8_3_1_930 16 28 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 28 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 28 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 28 163 (accept_3_3 14 28 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  28 163 (Polychromatic418967fa.accept_18_13_10_1_1_9025 13 28 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 28 163 (Polychromatic418967fa.accept_21_12_7_16_1_9024 12 28 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 28 163 (accept_3_3 11 28 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 28 163 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 28 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 28 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 28 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 28 163 (accept_3_3 8 28 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 28
  163 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 28 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 28 163 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 28 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 28 163 (accept_3_3 5 28 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 28 163 (Polychromatic418967fa.accept_16_4_12_3_1_2180 4 28 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 28 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 28
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 28 163 (accept_3_3 2 28 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 28 163 (Polychromatic418967fa.accept_10_1_8_3_1_947 1
  28 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 163))))))))))))))))))))))))))))
  (allB_succ 27 163 (allA_succ_of_accept 26 27 163 (accept_3_3 26 27 163 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 163 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 27 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 163 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 27 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 163 (accept_3_3 23 27 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 22
  27 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 163
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 27 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 27 163 (accept_3_3 20 27 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  27 163 (Polychromatic418967fa.accept_13_6_1_7_1_1690 19 27 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 27 163 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 27 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 163 (accept_3_3 17 27 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 27 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 163
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 27 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 27 163 (accept_3_3 14 27 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  27 163 (Polychromatic418967fa.accept_21_13_6_16_1_9023 13 27 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 27 163 (Polychromatic418967fa.accept_19_12_8_11_1_7554 12 27 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 163 (accept_3_3 11 27 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 27 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 163
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 27 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 27 163 (accept_3_3 8 27 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27
  163 (Polychromatic418967fa.accept_11_7_5_9_1_884 7 27 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 27 163 (Polychromatic418967fa.accept_10_6_7_3_1_547 6 27 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 163 (accept_3_3 5 27 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 27 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 27 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 163 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 27
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 163 (accept_3_3 2 27 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 163 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 27
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 163)))))))))))))))))))))))))))
  (allB_succ 26 163 (allA_of_3_1 26 26 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 25 163
  (allA_succ_of_accept 24 25 163 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 25 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 163 (accept_3_3 23 25 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 25 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 25 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 163 (Polychromatic418967fa.accept_9_3_7_1_1_143 21
  25 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 163 (accept_3_3 20 25
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 163
  (Polychromatic418967fa.accept_7_5_4_2_1_235 19 25 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 25 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 25 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 163 (accept_3_3 17 25 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 25 163 (Polychromatic418967fa.accept_14_2_11_9_1_2925 16 25 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 25 163
  (Polychromatic418967fa.accept_9_6_7_1_1_145 15 25 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 25 163 (accept_3_3 14 25 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  25 163 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 25 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 25 163 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 25 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 163 (accept_3_3 11 25 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 25 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 25 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 25 163
  (Polychromatic418967fa.accept_21_9_4_16_1_9022 9 25 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 25 163 (accept_3_3 8 25 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25
  163 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 25 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 25 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 25 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 25 163 (accept_3_3 5 25 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 25 163 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 25 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 163 (Polychromatic418967fa.accept_9_3_7_1_1_143 3
  25 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 163 (accept_3_3 2 25 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25 163 (Polychromatic418967fa.accept_15_1_10_13_1_939
  1 25 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 163)))))))))))))))))))))))))
  (allB_succ 24 163 (allA_succ_of_accept 23 24 163 (accept_3_3 23 24 163 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 24 163 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 24 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 24 163 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 24 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 24 163 (accept_3_3 20 24 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 24 163 (Polychromatic418967fa.accept_7_5_3_2_1_249 19
  24 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 24 163
  (Polychromatic418967fa.accept_11_7_2_9_1_480 18 24 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 24 163 (accept_3_3 17 24 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  24 163 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 24 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 24 163 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 24 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 24 163 (accept_3_3 14 24 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 163 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 24 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 24 163
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 24 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 24 163 (accept_3_3 11 24 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  24 163 (Polychromatic418967fa.accept_19_10_5_11_1_7597 10 24 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 24 163 (Polychromatic418967fa.accept_10_9_4_3_1_539 9 24 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 24 163 (accept_3_3 8 24 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 163 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 24 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 24 163
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 24 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 24 163 (accept_3_3 5 24 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24
  163 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 24 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 24 163 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 24 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 24 163 (accept_3_3 2 24 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 24 163 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 24 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 163)))))))))))))))))))))))) (allB_succ 23 163 (allA_of_3_1 23 23
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 22 163 (allA_succ_of_accept 21 22 163
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 22 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 22 163 (accept_3_3 20 22 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  22 163 (Polychromatic418967fa.accept_13_6_9_7_1_2430 19 22 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 22 163 (Polychromatic418967fa.accept_16_2_6_3_1_5396 18 22 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 163 (accept_3_3 17 22 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 22 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 22 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 22 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 22 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 22 163 (accept_3_3 14 22 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  22 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 22 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 22 163 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 22 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 22 163 (accept_3_3 11 22 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 22 163 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 22 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 22 163
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 22 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 22 163 (accept_3_3 8 22 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 22
  163 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 22 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 22 163 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 22 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 163 (accept_3_3 5 22 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 22 163 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 22 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 22 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 22
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 22 163 (accept_3_3 2 22 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 22 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 22
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 163)))))))))))))))))))))) (allB_succ 21
  163 (allA_succ_of_accept 20 21 163 (accept_3_3 20 21 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 21 163 (Polychromatic418967fa.accept_11_8_10_9_1_1401 19 21 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 21 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 21 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 163 (accept_3_3 17 21 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 21 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 163
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 21 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 21 163 (accept_3_3 14 21 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  21 163 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 21 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 21 163 (Polychromatic418967fa.accept_10_2_1_3_1_233 12 21 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 163 (accept_3_3 11 21 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 21 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 163
  (Polychromatic418967fa.accept_13_9_8_7_1_1073 9 21 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 21 163 (accept_3_3 8 21 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21
  163 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 21 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 21 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 21 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 163 (accept_3_3 5 21 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 21 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 21 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21 163 (Polychromatic418967fa.accept_12_3_9_7_1_472 3
  21 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 163 (accept_3_3 2 21 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 163 (Polychromatic418967fa.accept_11_1_10_9_1_871 1
  21 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 163))))))))))))))))))))) (allB_succ
  20 163 (allA_of_3_1 20 20 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 19 163 (allA_succ_of_accept 18 19
  163 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 19 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 163 (accept_3_3 17 19 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 163 (Polychromatic418967fa.accept_10_6_9_3_1_935 16 19 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 163 (Polychromatic418967fa.accept_17_15_2_10_1_9021 15 19 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 163 (accept_3_3 14 19 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 163 (Polychromatic418967fa.accept_21_13_19_16_1_721 13 19
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 163
  (Polychromatic418967fa.accept_13_12_6_7_1_1071 12 19 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 163 (accept_3_3 11 19 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 163 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 19 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 163 (Polychromatic418967fa.accept_13_9_6_7_1_551 9 19 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 163 (accept_3_3 8 19 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 163 (Polychromatic418967fa.accept_14_7_5_9_1_2911 7 19 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 163
  (Polychromatic418967fa.accept_10_6_9_3_1_935 6 19 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 163 (accept_3_3 5 19 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  163 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 19 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 163 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 19 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 163 (accept_3_3 2 19 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 163 (Polychromatic418967fa.accept_13_1_6_7_1_550 1 19 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 163))))))))))))))))))) (allB_succ 18 163 (allA_succ_of_accept 17
  18 163 (accept_3_3 17 18 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 163
  (Polychromatic418967fa.accept_10_6_8_3_1_930 16 18 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 18 163 (Polychromatic418967fa.accept_10_5_8_3_1_229 15 18 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 163 (accept_3_3 14 18 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 18 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 18 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 18 163 (Polychromatic418967fa.accept_7_5_4_2_1_235 12
  18 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 18 163 (accept_3_3 11 18
  163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 163
  (Polychromatic418967fa.accept_15_10_3_13_1_4480 10 18 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 18 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 18 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 163 (accept_3_3 8 18 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 18 163 (Polychromatic418967fa.accept_17_7_1_10_1_2836 7 18 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18 163 (Polychromatic418967fa.accept_7_6_4_2_1_236 6
  18 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 18 163 (accept_3_3 5 18 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 163 (Polychromatic418967fa.accept_19_4_18_11_1_7528
  4 18 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 18 163
  (Polychromatic418967fa.accept_19_3_18_11_1_6074 3 18 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 18 163 (accept_3_3 2 18 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18
  163 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 18 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 18 163)))))))))))))))))) (allB_succ 17 163 (allA_of_3_1 17 17 163 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 16 163 (allA_succ_of_accept 15 16 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 16 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 16 163 (accept_3_3 14 16 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 16 163 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 16 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 16 163
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 16 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 16 163 (accept_3_3 11 16 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  16 163 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 16 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 16 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 16 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 16 163 (accept_3_3 8 16 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 16 163 (Polychromatic418967fa.accept_10_7_6_3_1_927 7 16 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 16 163
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 16 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 16 163 (accept_3_3 5 16 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 16
  163 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 16 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 16 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 16 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 16 163 (accept_3_3 2 16 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 16 163 (Polychromatic418967fa.accept_13_1_3_7_1_1710 1 16 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 163)))))))))))))))) (allB_succ 15 163 (allA_succ_of_accept 14 15
  163 (accept_3_3 14 15 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 163
  (Polychromatic418967fa.accept_7_6_1_2_1_230 13 15 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 15 163 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 15 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 163 (accept_3_3 11 15 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 15 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 15 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 163 (Polychromatic418967fa.accept_12_9_3_7_1_924 9
  15 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 163 (accept_3_3 8 15 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 163 (Polychromatic418967fa.accept_9_7_6_1_1_709 7
  15 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 163
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 15 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 163 (accept_3_3 5 15 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15
  163 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 15 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 15 163 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 15 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 163 (accept_3_3 2 15 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 15 163 (Polychromatic418967fa.accept_19_1_15_11_1_4712 1 15 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 163))))))))))))))) (allB_succ 14 163 (allA_of_3_1 14 14 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 163 (allA_succ_of_accept 12 13 163
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 13 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 163 (accept_3_3 11 13 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 13 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 163 (Polychromatic418967fa.accept_17_9_13_10_1_1825 9 13 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 163 (accept_3_3 8 13 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 163 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 13 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 163
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 13 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 163 (accept_3_3 5 13 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  163 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 13 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 163 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 13 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 163 (accept_3_3 2 13 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 163 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 13 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 163))))))))))))) (allB_succ 12 163 (allA_succ_of_accept 11 12
  163 (accept_3_3 11 12 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 163
  (Polychromatic418967fa.accept_7_3_5_2_1_17 10 12 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 12 163 (Polychromatic418967fa.accept_16_9_12_3_1_3138 9 12 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 163 (accept_3_3 8 12 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 12 163 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 12 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12 163 (Polychromatic418967fa.accept_9_6_3_1_1_155 6
  12 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 12 163 (accept_3_3 5 12 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 163 (Polychromatic418967fa.accept_7_4_5_2_1_243 4
  12 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 12 163
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 12 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 12 163 (accept_3_3 2 12 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12
  163 (Polychromatic418967fa.accept_10_1_2_3_1_1910 1 12 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 12 163)))))))))))) (allB_succ 11 163 (allA_of_3_1 11 11 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 10 163 (allA_succ_of_accept 9 10 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 10 163
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 10 163 (accept_3_3 8 10 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 10 163 (Polychromatic418967fa.accept_16_7_10_3_1_2210
  7 10 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 10 163
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 10 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 10 163 (accept_3_3 5 10 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 10
  163 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 10 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 10 163 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 10 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 10 163 (accept_3_3 2 10 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 10 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 10 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 163)))))))))) (allB_succ 9 163 (allA_succ_of_accept 8
  9 163 (accept_3_3 8 9 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 163
  (Polychromatic418967fa.accept_15_7_9_13_1_3451 7 9 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 9 163 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 9 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 163 (accept_3_3 5 9 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 9 163 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 9 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 163 (Polychromatic418967fa.accept_12_3_9_7_1_472 3 9
  163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 163 (accept_3_3 2 9 163
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 163 (Polychromatic418967fa.accept_17_1_9_10_1_1864 1
  9 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 163))))))))) (allB_succ 8 163
  (allA_of_3_1 8 8 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 7 163 (allA_succ_of_accept 6 7 163
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 7 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 163 (accept_3_3 5 7 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 163
  (Polychromatic418967fa.accept_8_4_7_3_1_144 4 7 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 163 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 7 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 163 (accept_3_3 2 7 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 163 (Polychromatic418967fa.accept_17_1_7_10_1_1835 1 7 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 163))))))) (allB_succ 6 163 (allA_succ_of_accept 5 6 163
  (accept_3_3 5 6 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 6 163
  (Polychromatic418967fa.accept_7_4_6_2_1_451 4 6 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 6 163 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 6 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 6 163 (accept_3_3 2 6 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 6 163 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 6 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 163)))))) (allB_succ 5 163 (allA_of_3_1 5 5 163 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 4 163 (allA_succ_of_accept 3 4 163
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 4 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 163 (accept_3_3 2 4 163 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 163
  (Polychromatic418967fa.accept_16_1_4_3_1_3148 1 4 163 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 163)))) (allB_succ 3 163 (allA_succ_of_accept 2 3 163 (accept_3_3 2 3 163 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 163 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 3 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 163))) (allB_succ 2 163 (allA_of_3_1 2 2 163 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  163)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


