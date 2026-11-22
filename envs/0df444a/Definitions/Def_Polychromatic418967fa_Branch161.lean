-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch161
-- name    : Polychromatic418967fa_Branch161
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:17:50.224695+00:00
-- url     : https://prove2.me/theorems/8b80e579-22cd-4660-b5a2-6d0b8bc9d9ff
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

def Polychromatic418967fa.branch_161 : allB 161 161 :=
  allB_succ' 2 160 161 (Eq.refl Bool.true) (allA_of_3_0 2 160 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  159 161 (Eq.refl Bool.true) (allA_succ_of_accept 2 159 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 159 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 161 (accept_3_2 1 159 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 159 161))) (allB_succ' 4 158 161 (Eq.refl Bool.true)
  (allA_succ_of_accept 3 158 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 158 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 158 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 158 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 158 161 (accept_3_2 1 158 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158 161)))) (allB_succ' 5 157 161 (Eq.refl Bool.true) (allA_of_3_0
  5 157 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 6 156 161 (Eq.refl Bool.true) (allA_succ_of_accept 5
  156 161 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 156 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 156 161 (accept_3_2 4 156 161 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 156 161 (Polychromatic418967fa.accept_15_3_6_11_1_855 3 156 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 156 161 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 156 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 156 161 (accept_3_2 1 156 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156 161)))))) (allB_succ' 7 155 161 (Eq.refl Bool.true)
  (allA_succ_of_accept 6 155 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 155 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 155 161 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 155 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 155 161 (accept_3_2 4 155 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 155 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 3
  155 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 155 161
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 155 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 155 161 (accept_3_2 1 155 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 155 161)))))))
  (allB_succ' 8 154 161 (Eq.refl Bool.true) (allA_of_3_0 8 154 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  9 153 161 (Eq.refl Bool.true) (allA_succ_of_accept 8 153 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 153 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 161 (accept_3_2 7 153 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 153 161 (Polychromatic418967fa.accept_13_6_10_5_1_1648
  6 153 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 153 161
  (Polychromatic418967fa.accept_16_5_9_1_1_2070 5 153 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 153 161 (accept_3_2 4 153 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  153 161 (Polychromatic418967fa.accept_11_3_10_7_1_129 3 153 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 153 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 153 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 161 (accept_3_2 1 153 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 153 161))))))))) (allB_succ' 10 152 161 (Eq.refl Bool.true) (allA_succ_of_accept 9 152
  161 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 152 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 152 161 (Polychromatic418967fa.accept_21_8_5_14_1_5660 8 152 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 152 161 (accept_3_2 7 152 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 152 161 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 152 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 152 161 (Polychromatic418967fa.accept_11_5_9_7_1_411 5
  152 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 152 161 (accept_3_2 4 152
  161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 152 161 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 152 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 152 161
  (Polychromatic418967fa.accept_11_2_9_7_1_124 2 152 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 152 161 (accept_3_2 1 152 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152
  161)))))))))) (allB_succ' 11 151 161 (Eq.refl Bool.true) (allA_of_3_0 11 151 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 150 161 (Eq.refl Bool.true) (allA_succ_of_accept 11 150 161
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 150 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 150 161 (accept_3_2 10 150 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  150 161 (Polychromatic418967fa.accept_20_9_10_1_1_192 9 150 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 150 161 (Polychromatic418967fa.accept_19_8_17_9_1_4542 8 150 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 150 161 (accept_3_2 7 150 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 150 161 (Polychromatic418967fa.accept_17_6_14_8_1_3858 6 150
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 150 161
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 150 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 150 161 (accept_3_2 4 150 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  150 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 150 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 150 161 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 150 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 150 161 (accept_3_2 1 150 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 150 161)))))))))))) (allB_succ' 13 149 161 (Eq.refl Bool.true) (allA_succ_of_accept 12
  149 161 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 149 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 149 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 149 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 149 161 (accept_3_2 10 149 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 149 161 (Polychromatic418967fa.accept_16_9_5_1_1_1259 9 149 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 149 161
  (Polychromatic418967fa.accept_10_8_9_1_1_189 8 149 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 149 161 (accept_3_2 7 149 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  149 161 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 149 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 149 161 (Polychromatic418967fa.accept_10_5_9_1_1_187 5 149 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 149 161 (accept_3_2 4 149 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 149 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 149 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 149 161
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 149 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 149 161 (accept_3_2 1 149 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 149
  161))))))))))))) (allB_succ' 14 148 161 (Eq.refl Bool.true) (allA_of_3_0 14 148 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 147 161 (Eq.refl Bool.true) (allA_succ_of_gcd 14 147 161 7 2 21 23 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 147 161 (accept_3_2 13 147 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 147 161
  (Polychromatic418967fa.accept_13_12_4_5_1_1637 12 147 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 147 161 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 147 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 147 161 (accept_3_2 10 147 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 147 161 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 147 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 147 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 8
  147 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 147 161 7 1 21 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 147 161
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 147 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 147 161 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 147 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 147 161 (accept_3_2 4 147 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 147 161 (Polychromatic418967fa.accept_11_3_4_7_1_114 3 147 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 147 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 2
  147 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 161 (accept_3_2 1 147
  161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 147 161))))))))))))))) (allB_succ' 16 146 161 (Eq.refl
  Bool.true) (allA_succ_of_accept 15 146 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 146 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 146 161 (Polychromatic418967fa.accept_9_5_2_8_1_109
  14 146 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 146 161 (accept_3_2 13
  146 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 146 161
  (Polychromatic418967fa.accept_9_3_2_8_1_108 12 146 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 146 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 146 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 146 161 (accept_3_2 10 146 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 146 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 146 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 146 161 (Polychromatic418967fa.accept_12_8_2_5_1_844 8
  146 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 146 161 (accept_3_2 7 146
  161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 146 161
  (Polychromatic418967fa.accept_9_6_2_8_1_592 6 146 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 146 161 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 146 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 146 161 (accept_3_2 4 146 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 146 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 146 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 146 161 (Polychromatic418967fa.accept_10_2_6_1_1_1296
  2 146 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 146 161 (accept_3_2 1
  146 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146 161)))))))))))))))) (allB_succ' 17 145 161 (Eq.refl
  Bool.true) (allA_of_3_0 17 145 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 18 144 161 (Eq.refl Bool.true)
  (allA_succ_of_accept 17 144 161 (Polychromatic418967fa.accept_10_7_4_1_1_1319 17 144 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 144 161 (accept_3_2 16 144 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 144 161 (Polychromatic418967fa.accept_10_5_4_1_1_842 15 144 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 144 161
  (Polychromatic418967fa.accept_19_14_11_9_1_3330 14 144 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 144 161 (accept_3_2 13 144 161 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 144 161 (Polychromatic418967fa.accept_13_12_1_5_1_1650 12 144 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 144 161 (Polychromatic418967fa.accept_14_11_4_7_1_609 11 144
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 144 161 (accept_3_2 10 144
  161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 144 161
  (Polychromatic418967fa.accept_13_9_1_5_1_964 9 144 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 144 161 (Polychromatic418967fa.accept_13_8_1_5_1_3176 8 144 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 144 161 (accept_3_2 7 144 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 144 161 (Polychromatic418967fa.accept_11_6_1_7_1_1315 6 144 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 144 161 (Polychromatic418967fa.accept_10_5_4_1_1_842 5
  144 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 144 161 (accept_3_2 4 144
  161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 144 161
  (Polychromatic418967fa.accept_13_3_1_5_1_499 3 144 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 144 161 (Polychromatic418967fa.accept_15_2_9_11_1_1551 2 144 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 144 161 (accept_3_2 1 144 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 144 161)))))))))))))))))) (allB_succ' 19 143 161 (Eq.refl Bool.true) (allA_succ_of_accept 18 143
  161 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 143 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 143 161 (Polychromatic418967fa.accept_22_17_11_7_1_8898 17 143 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 143 161 (accept_3_2 16 143 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 143 161 (Polychromatic418967fa.accept_19_15_10_9_1_5956 15 143 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 143 161
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 143 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 143 161 (accept_3_2 13 143 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 143 161 (Polychromatic418967fa.accept_10_2_3_1_1_481 12 143 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 143 161 (Polychromatic418967fa.accept_14_11_3_7_1_604 11 143 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 143 161 (accept_3_2 10 143 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 143 161 (Polychromatic418967fa.accept_21_9_17_14_1_603 9 143
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 143 161
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 8 143 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 143 161 (accept_3_2 7 143 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  143 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 143 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 143 161 (Polychromatic418967fa.accept_15_5_8_11_1_2350 5 143 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 143 161 (accept_3_2 4 143 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 143 161 (Polychromatic418967fa.accept_15_3_8_11_1_4386 3 143
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 143 161
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 143 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 143 161 (accept_3_2 1 143 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 143
  161))))))))))))))))))) (allB_succ' 20 142 161 (Eq.refl Bool.true) (allA_of_3_0 20 142 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 21 141 161 (Eq.refl Bool.true) (allA_succ_of_accept 20 141 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 141 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 141 161 (accept_3_2 19 141 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 141 161 (Polychromatic418967fa.accept_15_3_6_11_1_855 18 141 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 141 161 (Polychromatic418967fa.accept_15_2_6_11_1_1587 17 141 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 141 161 (accept_3_2 16 141 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 141 161 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 141
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 141 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 141 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 141 161 (accept_3_2 13 141 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 141 161 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 141 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 141 161 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 141 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 141 161 (accept_3_2 10 141 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 141 161 (Polychromatic418967fa.accept_15_9_6_11_1_1586 9 141 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 141 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 141 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 141 161 (accept_3_2 7 141 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  141 161 (Polychromatic418967fa.accept_13_6_11_5_1_133 6 141 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 141 161 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 141 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 161 (accept_3_2 4 141 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 141 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 141 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 141 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 141 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 141 161 (accept_3_2 1 141 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 141
  161))))))))))))))))))))) (allB_succ' 22 140 161 (Eq.refl Bool.true) (allA_succ_of_gcd 21 140 161 7 3 20 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 140 161
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 140 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 140 161 (accept_3_2 19 140 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 140 161 (Polychromatic418967fa.accept_16_2_12_1_1_3086 18 140 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 140 161 (Polychromatic418967fa.accept_13_4_10_5_1_1644 17 140 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 140 161 (accept_3_2 16 140 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 140 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 140 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 140 161 7 2 20 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 140 161 (accept_3_2 13
  140 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 140 161
  (Polychromatic418967fa.accept_9_3_5_8_1_99 12 140 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 140 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 140 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 140 161 (accept_3_2 10 140 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 140 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 140 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 140 161 (Polychromatic418967fa.accept_13_8_10_5_1_977
  8 140 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 140 161 7 1 20 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 140 161
  (Polychromatic418967fa.accept_9_6_5_8_1_598 6 140 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 140 161 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 140 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 140 161 (accept_3_2 4 140 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 140 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 140 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 140 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 2
  140 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 140 161 (accept_3_2 1 140
  161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140 161)))))))))))))))))))))) (allB_succ' 23 139 161 (Eq.refl
  Bool.true) (allA_of_3_0 23 139 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 138 161 (Eq.refl Bool.true)
  (allA_succ_of_gcd 23 138 161 23 1 6 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 22 138 161 (accept_3_2 22 138 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 138 161 (Polychromatic418967fa.accept_15_6_3_11_1_848 21 138 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 138 161 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 138 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 138 161 (accept_3_2 19 138 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 138 161 (Polychromatic418967fa.accept_19_18_5_9_1_1112 18 138 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 138 161
  (Polychromatic418967fa.accept_20_17_18_1_1_8880 17 138 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 138 161 (accept_3_2 16 138 161 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 138 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 138 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 138 161 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 138 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 138 161 (accept_3_2 13 138 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 138 161 (Polychromatic418967fa.accept_11_1_6_7_1_116
  12 138 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 138 161
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 138 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 138 161 (accept_3_2 10 138 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  138 161 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 138 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 138 161 (Polychromatic418967fa.accept_15_8_3_11_1_849 8 138 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 138 161 (accept_3_2 7 138 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 138 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 138 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 138 161
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 138 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 138 161 (accept_3_2 4 138 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  138 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 138 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 138 161 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 138 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 138 161 (accept_3_2 1 138 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 138 161)))))))))))))))))))))))) (allB_succ' 25 137 161 (Eq.refl Bool.true)
  (allA_succ_of_accept 24 137 161 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 137 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 137 161 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 137 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 137 161 (accept_3_2 22 137 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 137 161 (Polychromatic418967fa.accept_9_3_2_8_1_108
  21 137 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 137 161
  (Polychromatic418967fa.accept_11_9_5_7_1_815 20 137 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 137 161 (accept_3_2 19 137 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 137 161 (Polychromatic418967fa.accept_14_4_11_7_1_1234 18 137 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 137 161 (Polychromatic418967fa.accept_14_3_11_7_1_1260 17 137 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 137 161 (accept_3_2 16 137 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 137 161 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 137 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 137 161
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 137 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 137 161 (accept_3_2 13 137 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 137 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 137 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 137 161 (Polychromatic418967fa.accept_13_11_7_5_1_2314 11 137 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 137 161 (accept_3_2 10 137 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 137 161 (Polychromatic418967fa.accept_11_9_5_7_1_815 9 137 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 161
  (Polychromatic418967fa.accept_16_8_9_1_1_7753 8 137 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 137 161 (accept_3_2 7 137 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  137 161 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 137 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 137 161 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 137 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 161 (accept_3_2 4 137 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 137 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 137 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 137 161
  (Polychromatic418967fa.accept_13_2_7_5_1_3189 2 137 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 137 161 (accept_3_2 1 137 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 137
  161))))))))))))))))))))))))) (allB_succ' 26 136 161 (Eq.refl Bool.true) (allA_of_3_0 26 136 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 27 135 161 (Eq.refl Bool.true) (allA_succ_of_accept 26 135 161
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 135 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 135 161 (accept_3_2 25 135 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 135 161 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 135 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 135 161 (Polychromatic418967fa.accept_19_4_2_9_1_4584 23 135 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 135 161 (accept_3_2 22 135 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 135 161 (Polychromatic418967fa.accept_11_10_3_7_1_2564 21 135
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 135 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 135 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 135 161 (accept_3_2 19 135 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 135 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 135 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 135 161 (Polychromatic418967fa.accept_19_17_2_9_1_4582 17 135 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 135 161 (accept_3_2 16 135 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 135 161 (Polychromatic418967fa.accept_11_4_3_7_1_828 15 135
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 135 161
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 135 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 135 161 (accept_3_2 13 135 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 135 161 (Polychromatic418967fa.accept_14_12_9_7_1_2762 12 135 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 135 161 (Polychromatic418967fa.accept_19_11_2_9_1_8897 11 135 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 135 161 (accept_3_2 10 135 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 135 161 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 135 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 135 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 135 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 135 161 (accept_3_2 7 135 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  135 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 135 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 135 161 (Polychromatic418967fa.accept_14_5_9_7_1_590 5 135 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 135 161 (accept_3_2 4 135 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 135 161 (Polychromatic418967fa.accept_21_3_9_14_1_5701 3 135 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 135 161
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 135 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 135 161 (accept_3_2 1 135 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135
  161))))))))))))))))))))))))))) (allB_succ' 28 134 161 (Eq.refl Bool.true) (allA_succ_of_accept 27 134 161
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 134 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 134 161 (Polychromatic418967fa.accept_20_6_14_1_1_8896 26 134 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 134 161 (accept_3_2 25 134 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 134 161 (Polychromatic418967fa.accept_19_5_1_9_1_8895 24 134 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 134 161
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 134 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 134 161 (accept_3_2 22 134 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 134 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 134 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 134 161 (Polychromatic418967fa.accept_11_9_2_7_1_1298 20 134 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 134 161 (accept_3_2 19 134 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 134 161 (Polychromatic418967fa.accept_15_3_14_11_1_1579 18 134
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 134 161
  (Polychromatic418967fa.accept_10_7_4_1_1_1319 17 134 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 134 161 (accept_3_2 16 134 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 134 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 134 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 134 161 (Polychromatic418967fa.accept_13_1_4_5_1_113 14 134 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 134 161 (accept_3_2 13 134 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 134 161 (Polychromatic418967fa.accept_13_12_4_5_1_1637 12 134
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 134 161
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 134 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 134 161 (accept_3_2 10 134 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  134 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 134 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 134 161 (Polychromatic418967fa.accept_12_8_2_5_1_844 8 134 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 134 161 (accept_3_2 7 134 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 134 161 (Polychromatic418967fa.accept_13_6_4_5_1_2330 6 134 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 134 161
  (Polychromatic418967fa.accept_10_5_4_1_1_842 5 134 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 134 161 (accept_3_2 4 134 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  134 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 134 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 134 161 (Polychromatic418967fa.accept_13_2_4_5_1_3152 2 134 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 134 161 (accept_3_2 1 134 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 134 161)))))))))))))))))))))))))))) (allB_succ' 29 133 161 (Eq.refl Bool.true)
  (allA_of_3_0 29 133 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 30 132 161 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 132 161 (Polychromatic418967fa.accept_8_5_4_1_1_111 29 132 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 132 161 (accept_3_2 28 132 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 132 161 (Polychromatic418967fa.accept_14_13_6_7_1_2013 27 132 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 132 161
  (Polychromatic418967fa.accept_10_6_2_1_1_494 26 132 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 132 161 (accept_3_2 25 132 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 132 161 (Polychromatic418967fa.accept_16_8_4_1_1_2102 24 132 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 132 161 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 132 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 132 161 (accept_3_2 22 132 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 132 161 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 132 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 132 161
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 132 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 132 161 (accept_3_2 19 132 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 132 161 (Polychromatic418967fa.accept_21_18_6_14_1_2812 18 132 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 132 161 (Polychromatic418967fa.accept_13_4_2_5_1_4045 17 132 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 132 161 (accept_3_2 16 132 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 132 161 (Polychromatic418967fa.accept_14_1_6_7_1_1936 15 132
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 132 161
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 132 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 132 161 (accept_3_2 13 132 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 132 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 132 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 132 161 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 132 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 132 161 (accept_3_2 10 132 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 132 161 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 132 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 132 161
  (Polychromatic418967fa.accept_14_8_6_7_1_1934 8 132 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 132 161 (accept_3_2 7 132 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  132 161 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 132 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 132 161 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 132 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 132 161 (accept_3_2 4 132 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 132 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 132 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 132 161
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 132 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 132 161 (accept_3_2 1 132 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132
  161)))))))))))))))))))))))))))))) (allB_succ' 31 131 161 (Eq.refl Bool.true) (allA_succ_of_accept 30 131 161
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 131 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 131 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 131 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 131 161 (accept_3_2 28 131 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 131 161 (Polychromatic418967fa.accept_17_10_12_8_1_2748 27 131 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 131 161
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 131 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 131 161 (accept_3_2 25 131 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 131 161 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 131 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 131 161 (Polychromatic418967fa.accept_14_9_5_7_1_1251 23 131 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 131 161 (accept_3_2 22 131 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 131 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 131 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 131 161
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 131 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 131 161 (accept_3_2 19 131 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 131 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 131 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 131 161 (Polychromatic418967fa.accept_13_4_1_5_1_1628 17 131 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 131 161 (accept_3_2 16 131 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 131 161 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 131 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 131 161
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 131 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 131 161 (accept_3_2 13 131 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 131 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 131 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 131 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 131 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 131 161 (accept_3_2 10 131 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 131 161 (Polychromatic418967fa.accept_13_9_1_5_1_964 9 131 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 131 161
  (Polychromatic418967fa.accept_13_8_1_5_1_3176 8 131 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 131 161 (accept_3_2 7 131 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  131 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 131 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 131 161 (Polychromatic418967fa.accept_17_5_12_8_1_6304 5 131 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 131 161 (accept_3_2 4 131 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 131 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 131 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 131 161
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 131 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 131 161 (accept_3_2 1 131 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 131
  161))))))))))))))))))))))))))))))) (allB_succ' 32 130 161 (Eq.refl Bool.true) (allA_of_3_0 32 130 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 129 161 (Eq.refl Bool.true) (allA_succ_of_accept 32 129 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 129 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 129 161 (accept_3_2 31 129 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 129 161 (Polychromatic418967fa.accept_13_4_12_5_1_476 30 129 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 129 161 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 129 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 129 161 (accept_3_2 28 129 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 129 161 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 129 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 129 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 129 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 129 161 (accept_3_2 25 129 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 129 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 129 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 129 161 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 129 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 161 (accept_3_2 22 129 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 129 161 (Polychromatic418967fa.accept_13_8_12_5_1_1604 21 129 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 129 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 129 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 129 161 (accept_3_2 19 129 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 129 161 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 129 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 129 161 (Polychromatic418967fa.accept_13_4_12_5_1_476 17 129 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 161 (accept_3_2 16 129 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 129 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 129 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 129 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 129 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 129 161 (accept_3_2 13 129 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 129 161 (Polychromatic418967fa.accept_10_2_9_1_1_185 12 129 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 129 161 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 129 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 161 (accept_3_2 10 129 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 129 161 (Polychromatic418967fa.accept_21_9_3_14_1_2806 9 129 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 129 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 129 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 129 161 (accept_3_2 7 129 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  129 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 129 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 129 161 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 129 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 161 (accept_3_2 4 129 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 129 161 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 129 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 129 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 129 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 129 161 (accept_3_2 1 129 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129
  161))))))))))))))))))))))))))))))))) (allB_succ' 34 128 161 (Eq.refl Bool.true) (allA_succ_of_accept 33 128 161
  (Polychromatic418967fa.accept_6_3_2_5_1_32 33 128 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 128 161 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 128 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 128 161 (accept_3_2 31 128 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 128 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 128 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 128 161 (Polychromatic418967fa.accept_10_9_8_1_1_1331
  29 128 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 128 161 (accept_3_2 28
  128 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 128 161
  (Polychromatic418967fa.accept_6_3_2_5_1_32 27 128 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 128 161 (Polychromatic418967fa.accept_12_2_8_5_1_408 26 128 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 128 161 (accept_3_2 25 128 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 128 161 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 128 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 128 161 (Polychromatic418967fa.accept_9_5_2_8_1_109
  23 128 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 128 161 (accept_3_2 22
  128 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 128 161
  (Polychromatic418967fa.accept_6_3_2_5_1_32 21 128 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 128 161 (Polychromatic418967fa.accept_13_7_11_5_1_2302 20 128 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 128 161 (accept_3_2 19 128 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 128 161 (Polychromatic418967fa.accept_15_3_8_11_1_4386 18 128 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 128 161
  (Polychromatic418967fa.accept_19_17_14_9_1_8833 17 128 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 128 161 (accept_3_2 16 128 161 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 128 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 128 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 128 161 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 128 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 128 161 (accept_3_2 13 128 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 128 161 (Polychromatic418967fa.accept_9_3_2_8_1_108
  12 128 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 128 161
  (Polychromatic418967fa.accept_17_11_9_8_1_5038 11 128 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 128 161 (accept_3_2 10 128 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  128 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 128 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 128 161 (Polychromatic418967fa.accept_18_8_2_17_1_4782 8 128 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 128 161 (accept_3_2 7 128 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 128 161 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 128 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 128 161
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 128 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 128 161 (accept_3_2 4 128 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  128 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 128 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 128 161 (Polychromatic418967fa.accept_12_2_8_5_1_408 2 128 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 128 161 (accept_3_2 1 128 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 128 161)))))))))))))))))))))))))))))))))) (allB_succ' 35 127 161 (Eq.refl Bool.true)
  (allA_of_3_0 35 127 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 126 161 (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 126 161 7 5 18 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 126 161 (accept_3_2 34 126 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 126 161 (Polychromatic418967fa.accept_15_3_6_11_1_855 33 126 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 126 161 (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 126 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 126 161 (accept_3_2 31 126 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 126 161 (Polychromatic418967fa.accept_13_4_9_5_1_1641 30 126
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 126 161
  (Polychromatic418967fa.accept_13_3_9_5_1_2340 29 126 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 126 161 7 4 18 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 126 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 126 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 126 161 (Polychromatic418967fa.accept_28_26_14_21_1_8894 26
  126 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 126 161 (accept_3_2 25
  126 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 126 161
  (Polychromatic418967fa.accept_15_9_6_11_1_1586 24 126 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 126 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 126 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 126 161 (accept_3_2 22 126 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 21 126 161 7 3 18 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 126 161 (Polychromatic418967fa.accept_11_9_5_7_1_815 20 126 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 126 161 (accept_3_2 19 126 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 126 161 (Polychromatic418967fa.accept_15_3_6_11_1_855 18 126
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 126 161
  (Polychromatic418967fa.accept_10_7_6_1_1_486 17 126 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 126 161 (accept_3_2 16 126 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 126 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 126 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 126 161 7 2 18 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 126 161 (accept_3_2 13 126 161 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 126 161 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 126 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 126 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 126 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 126 161 (accept_3_2 10 126 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 126 161 (Polychromatic418967fa.accept_11_9_5_7_1_815 9
  126 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 126 161
  (Polychromatic418967fa.accept_22_8_16_7_1_8893 8 126 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 126 161 7 1 18 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 126 161 (Polychromatic418967fa.accept_28_6_14_21_1_8892 6 126 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 126 161 (Polychromatic418967fa.accept_10_5_6_1_1_836 5 126 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 126 161 (accept_3_2 4 126 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 126 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 3
  126 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 126 161
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 126 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 126 161 (accept_3_2 1 126 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  161)))))))))))))))))))))))))))))))))))) (allB_succ' 37 125 161 (Eq.refl Bool.true) (allA_succ_of_accept 36 125 161
  (Polychromatic418967fa.accept_8_4_5_1_1_299 36 125 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 125 161 (Polychromatic418967fa.accept_16_3_13_1_1_1206 35 125 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 125 161 (accept_3_2 34 125 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 125 161 (Polychromatic418967fa.accept_19_14_11_9_1_3330 33 125 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 125 161
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 32 125 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 125 161 (accept_3_2 31 125 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 125 161 (Polychromatic418967fa.accept_11_8_4_7_1_1303 30 125 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 125 161 (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 125 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 125 161 (accept_3_2 28 125 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 125 161 (Polychromatic418967fa.accept_13_1_8_5_1_2315 27 125
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 125 161
  (Polychromatic418967fa.accept_10_6_5_1_1_482 26 125 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 125 161 (accept_3_2 25 125 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 125 161 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 125 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 125 161 (Polychromatic418967fa.accept_13_10_8_5_1_1616 23 125 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 125 161 (accept_3_2 22 125 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 125 161 (Polychromatic418967fa.accept_15_6_5_11_1_2378 21 125
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 125 161
  (Polychromatic418967fa.accept_8_4_5_1_1_299 20 125 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 125 161 (accept_3_2 19 125 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 125 161 (Polychromatic418967fa.accept_21_18_20_14_1_5711 18 125 161 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 17 125 161 (Polychromatic418967fa.accept_15_2_5_11_1_1563 17 125 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 125 161 (accept_3_2 16 125 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 125 161
  (Polychromatic418967fa.accept_14_1_13_7_1_1205 15 125 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 125 161 (Polychromatic418967fa.accept_10_4_5_1_1_497 14 125 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 125 161 (accept_3_2 13 125 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 125 161 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 125 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 125 161
  (Polychromatic418967fa.accept_21_11_20_14_1_4179 11 125 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 125 161 (accept_3_2 10 125 161 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 125 161 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 125 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 125 161 (Polychromatic418967fa.accept_11_8_4_7_1_1303 8 125 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 125 161 (accept_3_2 7 125 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 125 161 (Polychromatic418967fa.accept_10_6_5_1_1_482 6
  125 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 125 161
  (Polychromatic418967fa.accept_16_5_13_1_1_2084 5 125 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 125 161 (accept_3_2 4 125 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  125 161 (Polychromatic418967fa.accept_11_3_4_7_1_114 3 125 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 125 161 (Polychromatic418967fa.accept_15_2_5_11_1_1563 2 125 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 125 161 (accept_3_2 1 125 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 125 161))))))))))))))))))))))))))))))))))))) (allB_succ' 38 124 161 (Eq.refl
  Bool.true) (allA_of_3_0 38 124 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 123 161 (Eq.refl Bool.true)
  (allA_succ_of_accept 38 123 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 123 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 123 161 (accept_3_2 37 123 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 123 161 (Polychromatic418967fa.accept_13_10_6_5_1_2297 36 123 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 123 161
  (Polychromatic418967fa.accept_17_1_4_8_1_5049 35 123 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 123 161 (accept_3_2 34 123 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 123 161 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 123 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 123 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 123 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 161 (accept_3_2 31 123 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 123 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 123 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 123 161
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 123 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 123 161 (accept_3_2 28 123 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 123 161 (Polychromatic418967fa.accept_13_1_6_5_1_1610 27 123 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 123 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 123 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 161 (accept_3_2 25 123 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 123 161 (Polychromatic418967fa.accept_13_11_6_5_1_2339 24 123 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 123 161
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 123 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 123 161 (accept_3_2 22 123 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 123 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 123 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 123 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 123 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 161 (accept_3_2 19 123 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 123 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 123 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 123 161
  (Polychromatic418967fa.accept_13_4_6_5_1_2333 17 123 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 123 161 (accept_3_2 16 123 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 123 161 (Polychromatic418967fa.accept_16_15_11_1_1_7767 15 123 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 123 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 123 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 161 (accept_3_2 13 123 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 123 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 123 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 123 161
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 123 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 123 161 (accept_3_2 10 123 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  123 161 (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 123 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 123 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 123 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 161 (accept_3_2 7 123 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 123 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 123 161
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 123 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 123 161 (accept_3_2 4 123 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  123 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 123 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 123 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 123 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 161 (accept_3_2 1 123 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 123 161))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 122 161 (Eq.refl
  Bool.true) (allA_succ_of_accept 39 122 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 122 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 122 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 38
  122 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 122 161 (accept_3_2 37
  122 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 122 161
  (Polychromatic418967fa.accept_10_6_2_1_1_494 36 122 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 122 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 122 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 122 161 (accept_3_2 34 122 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 122 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 122 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 122 161 (Polychromatic418967fa.accept_12_8_2_5_1_844
  32 122 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 122 161 (accept_3_2 31
  122 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 122 161
  (Polychromatic418967fa.accept_9_3_5_8_1_99 30 122 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 122 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 122 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 122 161 (accept_3_2 28 122 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 122 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 122 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 122 161 (Polychromatic418967fa.accept_10_6_2_1_1_494
  26 122 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 122 161 (accept_3_2 25
  122 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 122 161
  (Polychromatic418967fa.accept_9_6_5_8_1_598 24 122 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 122 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 122 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 122 161 (accept_3_2 22 122 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 122 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 122 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 122 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 20
  122 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 122 161 (accept_3_2 19
  122 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 122 161
  (Polychromatic418967fa.accept_14_4_10_7_1_1946 18 122 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 122 161 (Polychromatic418967fa.accept_11_6_1_7_1_1315 17 122 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 122 161 (accept_3_2 16 122 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 122 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 122 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 122 161
  (Polychromatic418967fa.accept_19_14_8_9_1_4547 14 122 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 122 161 (accept_3_2 13 122 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 122 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 122 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 122 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 122 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 122 161 (accept_3_2 10 122 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 122 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 122 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 122 161
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 122 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 122 161 (accept_3_2 7 122 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  122 161 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 122 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 122 161 (Polychromatic418967fa.accept_15_5_2_11_1_1596 5 122 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 122 161 (accept_3_2 4 122 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 122 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 122 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 122 161
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 122 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 122 161 (accept_3_2 1 122 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  161)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 121 161 (Eq.refl Bool.true) (allA_of_3_0 41 121 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 120 161 (Eq.refl Bool.true) (allA_succ_of_accept 41 120 161
  (Polychromatic418967fa.accept_9_5_3_8_1_316 41 120 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 120 161 (accept_3_2 40 120 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 120 161 (Polychromatic418967fa.accept_16_7_8_1_1_3061 39 120 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 120 161 (Polychromatic418967fa.accept_9_2_3_8_1_318 38 120 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 120 161 (accept_3_2 37 120 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 120 161 (Polychromatic418967fa.accept_11_3_10_7_1_129 36 120 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 120 161
  (Polychromatic418967fa.accept_13_9_3_5_1_1605 35 120 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 120 161 (accept_3_2 34 120 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 120 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 120 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 120 161 (Polychromatic418967fa.accept_9_5_3_8_1_316 32 120 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 120 161 (accept_3_2 31 120 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 120 161 (Polychromatic418967fa.accept_21_9_15_14_1_2790 30 120 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 120 161
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 120 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 120 161 (accept_3_2 28 120 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 120 161 (Polychromatic418967fa.accept_13_1_3_5_1_140 27 120 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 120 161 (Polychromatic418967fa.accept_17_9_1_8_1_5045 26 120 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 120 161 (accept_3_2 25 120 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 120 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 120 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 120 161
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 120 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 120 161 (accept_3_2 22 120 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 120 161 (Polychromatic418967fa.accept_13_8_3_5_1_1636 21 120 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 120 161 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 120 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 120 161 (accept_3_2 19 120 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 120 161 (Polychromatic418967fa.accept_19_18_6_9_1_5991 18 120 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 120 161
  (Polychromatic418967fa.accept_19_17_6_9_1_8856 17 120 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 120 161 (accept_3_2 16 120 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 120 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 120 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 120 161 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 120 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 120 161 (accept_3_2 13 120 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 120 161 (Polychromatic418967fa.accept_16_12_8_1_1_5270 12 120 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 120 161
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 120 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 120 161 (accept_3_2 10 120 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  120 161 (Polychromatic418967fa.accept_13_9_3_5_1_1605 9 120 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 120 161 (Polychromatic418967fa.accept_13_8_3_5_1_1636 8 120 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 120 161 (accept_3_2 7 120 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 120 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 120 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 120 161
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 120 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 120 161 (accept_3_2 4 120 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  120 161 (Polychromatic418967fa.accept_11_3_10_7_1_129 3 120 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 120 161 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 120 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 120 161 (accept_3_2 1 120 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 120 161)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 119 161 (Eq.refl
  Bool.true) (allA_succ_of_gcd 42 119 161 7 6 17 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 119 161 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 119 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 119 161 (accept_3_2 40 119 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 119 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 119 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 119 161
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 119 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 119 161 (accept_3_2 37 119 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 119 161 (Polychromatic418967fa.accept_13_10_2_5_1_1633 36 119 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 119 161 7 5 17 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 34 119 161 (accept_3_2 34 119 161 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 119 161 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 119 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 119 161 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 119 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 119 161 (accept_3_2 31 119 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 119 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 30
  119 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 119 161
  (Polychromatic418967fa.accept_13_3_2_5_1_1632 29 119 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 119 161 7 4 17 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 119 161 (Polychromatic418967fa.accept_11_5_9_7_1_411 27 119 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 119 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 119 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 119 161 (accept_3_2 25 119 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 119 161 (Polychromatic418967fa.accept_9_6_2_8_1_592
  24 119 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 119 161
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 119 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 119 161 (accept_3_2 22 119 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21
  119 161 7 3 17 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  20 119 161 (Polychromatic418967fa.accept_13_7_2_5_1_2344 20 119 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 119 161 (accept_3_2 19 119 161 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 119 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 119 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 119 161 (Polychromatic418967fa.accept_13_4_2_5_1_4045 17 119
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 119 161 (accept_3_2 16 119
  161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 119 161
  (Polychromatic418967fa.accept_9_6_2_8_1_592 15 119 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 119 161 7 2 17 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 119 161 (accept_3_2 13 119 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 119 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 119 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 119 161 (Polychromatic418967fa.accept_24_11_23_17_1_7012 11 119 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 161 (accept_3_2 10 119 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 119 161 (Polychromatic418967fa.accept_13_9_2_5_1_2310 9 119 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 161
  (Polychromatic418967fa.accept_10_8_9_1_1_189 8 119 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 119 161 7 1 17 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 119 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 119 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 119 161 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 119 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 161 (accept_3_2 4 119 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 119 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 3
  119 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 161
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 119 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 119 161 (accept_3_2 1 119 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  161))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 118 161 (Eq.refl Bool.true) (allA_of_3_0 44 118 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 117 161 (Eq.refl Bool.true) (allA_succ_of_accept 44 117 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 117 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 117 161 (accept_3_2 43 117 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 117 161 (Polychromatic418967fa.accept_28_14_5_21_1_8891 42 117 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 117 161 (Polychromatic418967fa.accept_16_9_5_1_1_1259 41 117 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 117 161 (accept_3_2 40 117 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 117 161 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 117
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 117 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 117 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 117 161 (accept_3_2 37 117 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 117 161 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 117 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 117 161 (Polychromatic418967fa.accept_25_10_17_11_1_8890 35 117 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 161 (accept_3_2 34 117 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 117 161 (Polychromatic418967fa.accept_18_15_9_17_1_6043 33 117
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 117 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 117 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 117 161 (accept_3_2 31 117 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 117 161 (Polychromatic418967fa.accept_14_2_5_7_1_3767 30 117 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 117 161 (Polychromatic418967fa.accept_15_14_12_11_1_1572 29 117 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 161 (accept_3_2 28 117 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 117 161 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 117
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 117 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 117 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 117 161 (accept_3_2 25 117 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 117 161 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 117 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 117 161 (Polychromatic418967fa.accept_14_9_5_7_1_1251 23 117 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 161 (accept_3_2 22 117 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 117 161 (Polychromatic418967fa.accept_26_21_13_5_1_8889 21 117
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 117 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 117 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 117 161 (accept_3_2 19 117 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 117 161 (Polychromatic418967fa.accept_19_18_3_9_1_3333 18 117 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 117 161 (Polychromatic418967fa.accept_27_17_9_26_1_8888 17 117 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 161 (accept_3_2 16 117 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 117 161 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 117
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 117 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 117 161 (accept_3_2 13 117 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 117 161 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 117 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 117 161 (Polychromatic418967fa.accept_19_11_3_9_1_8882 11 117 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 161 (accept_3_2 10 117 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 161 (Polychromatic418967fa.accept_14_9_5_7_1_1251 9 117 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 117 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 117 161 (accept_3_2 7 117 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  117 161 (Polychromatic418967fa.accept_10_6_7_1_1_1297 6 117 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 117 161 (Polychromatic418967fa.accept_21_5_12_14_1_7241 5 117 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 161 (accept_3_2 4 117 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 117 161 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 117 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 117 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 117 161 (accept_3_2 1 117 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  161))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 116 161 (Eq.refl Bool.true) (allA_succ_of_accept 45
  116 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 116 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 116 161 (Polychromatic418967fa.accept_16_12_4_1_1_1257 44 116 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 116 161 (accept_3_2 43 116 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 116 161 (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 116
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 116 161
  (Polychromatic418967fa.accept_13_2_12_5_1_1602 41 116 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 116 161 (accept_3_2 40 116 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 116 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 116 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 116 161 (Polychromatic418967fa.accept_12_2_8_5_1_408 38 116 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 116 161 (accept_3_2 37 116 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 116 161 (Polychromatic418967fa.accept_19_17_2_9_1_4582 36 116
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 116 161
  (Polychromatic418967fa.accept_10_5_6_1_1_836 35 116 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 116 161 (accept_3_2 34 116 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 116 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 116 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 116 161 (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 116 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 116 161 (accept_3_2 31 116 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 116 161 (Polychromatic418967fa.accept_13_4_12_5_1_476 30 116
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 116 161
  (Polychromatic418967fa.accept_8_5_4_1_1_111 29 116 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 116 161 (accept_3_2 28 116 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 116 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 116 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 116 161 (Polychromatic418967fa.accept_12_2_8_5_1_408 26 116 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 116 161 (accept_3_2 25 116 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 116 161 (Polychromatic418967fa.accept_14_10_4_7_1_1214 24 116
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 116 161
  (Polychromatic418967fa.accept_11_1_6_7_1_116 23 116 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 116 161 (accept_3_2 22 116 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 116 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 116 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 116 161 (Polychromatic418967fa.accept_13_7_12_5_1_1603 20 116 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 116 161 (accept_3_2 19 116 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 116 161 (Polychromatic418967fa.accept_19_18_2_9_1_8870 18 116
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 116 161
  (Polychromatic418967fa.accept_10_7_6_1_1_486 17 116 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 116 161 (accept_3_2 16 116 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 116 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 116 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 116 161 (Polychromatic418967fa.accept_12_2_8_5_1_408 14 116 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 116 161 (accept_3_2 13 116 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 116 161 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 116
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 116 161
  (Polychromatic418967fa.accept_14_11_4_7_1_609 11 116 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 116 161 (accept_3_2 10 116 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  116 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 116 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 116 161 (Polychromatic418967fa.accept_13_8_12_5_1_1604 8 116 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 116 161 (accept_3_2 7 116 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 116 161 (Polychromatic418967fa.accept_13_6_12_5_1_2304 6 116
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 116 161
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 116 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 116 161 (accept_3_2 4 116 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  116 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 116 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 116 161 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 116 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 116 161 (accept_3_2 1 116 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 116 161)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 115 161 (Eq.refl
  Bool.true) (allA_of_3_0 47 115 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 114 161 (Eq.refl Bool.true)
  (allA_succ_of_accept 47 114 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 114 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 114 161 (accept_3_2 46 114 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 114 161 (Polychromatic418967fa.accept_10_5_4_1_1_842 45 114 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 114 161
  (Polychromatic418967fa.accept_16_12_2_1_1_1215 44 114 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 114 161 (accept_3_2 43 114 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 114 161 (Polychromatic418967fa.accept_27_15_6_26_1_8887 42 114 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 114 161 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 114 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 114 161 (accept_3_2 40 114 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 114 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 114 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 114 161
  (Polychromatic418967fa.accept_9_2_6_8_1_321 38 114 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 114 161 (accept_3_2 37 114 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 114 161 (Polychromatic418967fa.accept_11_3_4_7_1_114 36 114 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 114 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 114 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 114 161 (accept_3_2 34 114 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 114 161 (Polychromatic418967fa.accept_14_5_2_7_1_2804 33 114 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 114 161
  (Polychromatic418967fa.accept_9_5_6_8_1_101 32 114 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 114 161 (accept_3_2 31 114 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 114 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 114 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 114 161 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 114 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 114 161 (accept_3_2 28 114 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 114 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 114 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 114 161
  (Polychromatic418967fa.accept_14_12_2_7_1_1243 26 114 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 114 161 (accept_3_2 25 114 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 114 161 (Polychromatic418967fa.accept_21_3_9_14_1_5701 24 114 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 114 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 114 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 114 161 (accept_3_2 22 114 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 114 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 114 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 114 161
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 114 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 114 161 (accept_3_2 19 114 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 114 161 (Polychromatic418967fa.accept_21_18_9_14_1_8832 18 114 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 114 161 (Polychromatic418967fa.accept_10_7_4_1_1_1319 17 114 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 114 161 (accept_3_2 16 114 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 114 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 114 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 114 161
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 114 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 114 161 (accept_3_2 13 114 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 114 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 114 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 114 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 114 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 114 161 (accept_3_2 10 114 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 114 161 (Polychromatic418967fa.accept_14_9_2_7_1_1242 9 114 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 114 161
  (Polychromatic418967fa.accept_11_8_4_7_1_1303 8 114 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 114 161 (accept_3_2 7 114 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  114 161 (Polychromatic418967fa.accept_13_6_10_5_1_1648 6 114 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 114 161 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 114 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 114 161 (accept_3_2 4 114 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 114 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 114 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 114 161
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 114 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 114 161 (accept_3_2 1 114 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  161)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 113 161 (Eq.refl Bool.true) (allA_succ_of_accept 48
  113 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 113 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 113 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 113 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 113 161 (accept_3_2 46 113 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 113 161 (Polychromatic418967fa.accept_21_3_8_14_1_8864 45 113 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 113 161
  (Polychromatic418967fa.accept_18_8_5_17_1_1388 44 113 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 113 161 (accept_3_2 43 113 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 113 161 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 113 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 113 161 (Polychromatic418967fa.accept_13_2_9_5_1_959 41 113 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 113 161 (accept_3_2 40 113 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 113 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 113 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 113 161
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 113 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 113 161 (accept_3_2 37 113 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 113 161 (Polychromatic418967fa.accept_14_8_1_7_1_3725 36 113 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 113 161 (Polychromatic418967fa.accept_15_5_8_11_1_2350 35 113 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 113 161 (accept_3_2 34 113 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 113 161 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 113 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 113 161
  (Polychromatic418967fa.accept_10_2_3_1_1_481 32 113 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 113 161 (accept_3_2 31 113 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 113 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 113 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 113 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 113 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 113 161 (accept_3_2 28 113 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 113 161 (Polychromatic418967fa.accept_13_1_9_5_1_1598 27 113 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 113 161
  (Polychromatic418967fa.accept_11_4_3_7_1_828 26 113 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 113 161 (accept_3_2 25 113 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 113 161 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 113 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 113 161 (Polychromatic418967fa.accept_20_3_13_1_1_8886 23 113 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 113 161 (accept_3_2 22 113 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 113 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 113 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 161
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 113 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 113 161 (accept_3_2 19 113 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 113 161 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 113 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 113 161 (Polychromatic418967fa.accept_13_4_9_5_1_1641 17 113 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 161 (accept_3_2 16 113 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 113 161 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 113 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 161
  (Polychromatic418967fa.accept_13_1_9_5_1_1598 14 113 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 113 161 (accept_3_2 13 113 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 113 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 113 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 113 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 113 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 161 (accept_3_2 10 113 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 161 (Polychromatic418967fa.accept_17_9_11_8_1_5077 9 113 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 161
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 8 113 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 113 161 (accept_3_2 7 113 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  113 161 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 113 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 113 161 (Polychromatic418967fa.accept_15_5_8_11_1_2350 5 113 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 161 (accept_3_2 4 113 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 113 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 161
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 113 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 161 (accept_3_2 1 113 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  161))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 112 161 (Eq.refl Bool.true) (allA_of_3_0 50 112
  161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 111 161 (Eq.refl Bool.true) (allA_succ_of_accept 50 111
  161 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 111 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 111 161 (accept_3_2 49 111 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 111 161 (Polychromatic418967fa.accept_14_6_13_7_1_2015 48 111 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 111 161 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 111 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 111 161 (accept_3_2 46 111 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 111 161 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 111 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 111 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 111 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 111 161 (accept_3_2 43 111 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 111 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 111 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 111 161 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 111 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 111 161 (accept_3_2 40 111 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 111 161 (Polychromatic418967fa.accept_11_6_1_7_1_1315 39 111 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 111 161
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 111 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 111 161 (accept_3_2 37 111 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 111 161 (Polychromatic418967fa.accept_14_8_13_7_1_2798 36 111 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 111 161 (Polychromatic418967fa.accept_15_5_6_11_1_854 35 111 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 111 161 (accept_3_2 34 111 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 111 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 111 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 111 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 111 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 111 161 (accept_3_2 31 111 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 111 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 111 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 111 161 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 111 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 161 (accept_3_2 28 111 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 111 161 (Polychromatic418967fa.accept_16_11_15_1_1_2074 27 111 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 111 161
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 111 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 111 161 (accept_3_2 25 111 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 111 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 111 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 111 161 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 111 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 111 161 (accept_3_2 22 111 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 111 161 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 111 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 111 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 111 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 111 161 (accept_3_2 19 111 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 111 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 111 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 111 161 (Polychromatic418967fa.accept_11_6_1_7_1_1315 17 111 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 161 (accept_3_2 16 111 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 111 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 111 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 111 161
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 111 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 111 161 (accept_3_2 13 111 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 111 161 (Polychromatic418967fa.accept_13_12_7_5_1_3147 12 111 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 111 161 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 111 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 161 (accept_3_2 10 111 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 111 161 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 111 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 111 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 111 161 (accept_3_2 7 111 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  111 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 111 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 111 161 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 111 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 161 (accept_3_2 4 111 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 111 161 (Polychromatic418967fa.accept_15_3_6_11_1_855 3 111 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 161
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 111 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 111 161 (accept_3_2 1 111 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111
  161))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 110 161 (Eq.refl Bool.true) (allA_succ_of_accept
  51 110 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 110 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 110 161 (Polychromatic418967fa.accept_9_5_2_8_1_109 50 110 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 110 161 (accept_3_2 49 110 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 110 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 110 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 110 161
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 110 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 110 161 (accept_3_2 46 110 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 110 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 110 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 110 161 (Polychromatic418967fa.accept_12_8_2_5_1_844 44 110 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 110 161 (accept_3_2 43 110 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 110 161 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 110 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 110 161
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 110 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 110 161 (accept_3_2 40 110 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 110 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 110 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 110 161 (Polychromatic418967fa.accept_13_12_6_5_1_2335 38 110 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 110 161 (accept_3_2 37 110 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 110 161 (Polychromatic418967fa.accept_13_10_6_5_1_2297 36 110
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 110 161
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 110 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 110 161 (accept_3_2 34 110 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 110 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 110 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 110 161 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 110 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 110 161 (accept_3_2 31 110 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 110 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 110 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 110 161
  (Polychromatic418967fa.accept_13_3_6_5_1_2336 29 110 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 110 161 (accept_3_2 28 110 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 110 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 110 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 110 161 (Polychromatic418967fa.accept_18_8_2_17_1_4782 26 110 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 110 161 (accept_3_2 25 110 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 110 161 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 110 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 110 161
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 110 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 110 161 (accept_3_2 22 110 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 110 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 110 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 110 161 (Polychromatic418967fa.accept_12_8_2_5_1_844 20 110 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 110 161 (accept_3_2 19 110 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 110 161 (Polychromatic418967fa.accept_19_18_15_9_1_3310 18 110
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 110 161
  (Polychromatic418967fa.accept_13_4_6_5_1_2333 17 110 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 110 161 (accept_3_2 16 110 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 110 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 110 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 110 161 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 110 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 110 161 (accept_3_2 13 110 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 110 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 110 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 110 161
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 110 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 110 161 (accept_3_2 10 110 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  110 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 110 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 110 161 (Polychromatic418967fa.accept_12_8_2_5_1_844 8 110 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 110 161 (accept_3_2 7 110 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 110 161 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 110 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 110 161
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 110 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 110 161 (accept_3_2 4 110 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  110 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 110 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 110 161 (Polychromatic418967fa.accept_14_2_12_7_1_617 2 110 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 110 161 (accept_3_2 1 110 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 110 161)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 109 161
  (Eq.refl Bool.true) (allA_of_3_0 53 109 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 54 108 161 (Eq.refl
  Bool.true) (allA_succ_of_accept 53 108 161 (Polychromatic418967fa.accept_8_5_4_1_1_111 53 108 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 108 161 (accept_3_2 52 108 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 108 161 (Polychromatic418967fa.accept_13_12_4_5_1_1637 51 108 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 108 161
  (Polychromatic418967fa.accept_16_2_12_1_1_3086 50 108 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 108 161 (accept_3_2 49 108 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 108 161 (Polychromatic418967fa.accept_13_9_4_5_1_1651 48 108 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 108 161 (Polychromatic418967fa.accept_20_7_8_1_1_5856 47 108 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 108 161 (accept_3_2 46 108 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 108 161 (Polychromatic418967fa.accept_8_5_4_1_1_111 45 108 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 108 161
  (Polychromatic418967fa.accept_15_14_3_11_1_850 44 108 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 108 161 (accept_3_2 43 108 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 108 161 (Polychromatic418967fa.accept_19_4_13_9_1_5968 42 108 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 108 161 (Polychromatic418967fa.accept_13_2_4_5_1_3152 41 108 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 108 161 (accept_3_2 40 108 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 108 161 (Polychromatic418967fa.accept_10_9_8_1_1_1331 39 108
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 108 161
  (Polychromatic418967fa.accept_11_5_9_7_1_411 38 108 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 108 161 (accept_3_2 37 108 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 108 161 (Polychromatic418967fa.accept_13_10_4_5_1_2331 36 108 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 108 161 (Polychromatic418967fa.accept_11_2_9_7_1_124 35 108 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 108 161 (accept_3_2 34 108 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 108 161 (Polychromatic418967fa.accept_10_3_8_1_1_182 33 108
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 108 161
  (Polychromatic418967fa.accept_13_6_4_5_1_2330 32 108 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 108 161 (accept_3_2 31 108 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 108 161 (Polychromatic418967fa.accept_21_9_3_14_1_2806 30 108 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 108 161 (Polychromatic418967fa.accept_8_5_4_1_1_111 29 108 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 108 161 (accept_3_2 28 108 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 108 161 (Polychromatic418967fa.accept_11_5_9_7_1_411 27 108 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 108 161
  (Polychromatic418967fa.accept_17_9_6_8_1_6315 26 108 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 108 161 (accept_3_2 25 108 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 108 161 (Polychromatic418967fa.accept_11_2_9_7_1_124 24 108 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 108 161 (Polychromatic418967fa.accept_10_3_8_1_1_182 23 108 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 108 161 (accept_3_2 22 108 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 108 161 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 108 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 108 161
  (Polychromatic418967fa.accept_16_4_12_1_1_1204 20 108 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 108 161 (accept_3_2 19 108 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 108 161 (Polychromatic418967fa.accept_14_4_10_7_1_1946 18 108 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 108 161 (Polychromatic418967fa.accept_14_3_10_7_1_3773 17 108 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 108 161 (accept_3_2 16 108 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 108 161 (Polychromatic418967fa.accept_13_2_4_5_1_3152 15 108
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 108 161
  (Polychromatic418967fa.accept_13_1_4_5_1_113 14 108 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 108 161 (accept_3_2 13 108 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 108 161 (Polychromatic418967fa.accept_13_12_4_5_1_1637 12 108 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 108 161 (Polychromatic418967fa.accept_14_11_10_7_1_1948 11 108 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 108 161 (accept_3_2 10 108 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 108 161 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 108 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 108 161
  (Polychromatic418967fa.accept_15_8_3_11_1_849 8 108 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 108 161 (accept_3_2 7 108 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  108 161 (Polychromatic418967fa.accept_13_6_4_5_1_2330 6 108 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 108 161 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 108 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 108 161 (accept_3_2 4 108 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 108 161 (Polychromatic418967fa.accept_10_3_8_1_1_182 3 108 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 108 161
  (Polychromatic418967fa.accept_11_2_9_7_1_124 2 108 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 108 161 (accept_3_2 1 108 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  161)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 107 161 (Eq.refl Bool.true)
  (allA_succ_of_accept 54 107 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 107 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 107 161 (Polychromatic418967fa.accept_13_1_3_5_1_140 53 107
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 107 161 (accept_3_2 52 107
  161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 107 161
  (Polychromatic418967fa.accept_15_6_2_11_1_325 51 107 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 107 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 107 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 107 161 (accept_3_2 49 107 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 107 161 (Polychromatic418967fa.accept_11_4_8_7_1_819 48 107 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 107 161
  (Polychromatic418967fa.accept_13_8_3_5_1_1636 47 107 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 107 161 (accept_3_2 46 107 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 107 161 (Polychromatic418967fa.accept_13_6_3_5_1_3167 45 107 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 107 161 (Polychromatic418967fa.accept_10_4_7_1_1_471 44 107 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 107 161 (accept_3_2 43 107 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 107 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 107 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 107 161
  (Polychromatic418967fa.accept_13_2_3_5_1_2294 41 107 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 107 161 (accept_3_2 40 107 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 107 161 (Polychromatic418967fa.accept_15_9_2_11_1_2391 39 107 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 107 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 107 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 107 161 (accept_3_2 37 107 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 107 161 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 107 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 107 161
  (Polychromatic418967fa.accept_13_9_3_5_1_1605 35 107 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 107 161 (accept_3_2 34 107 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 107 161 (Polychromatic418967fa.accept_14_5_9_7_1_590 33 107 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 107 161 (Polychromatic418967fa.accept_13_6_3_5_1_3167 32 107 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 107 161 (accept_3_2 31 107 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 107 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 107 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 107 161
  (Polychromatic418967fa.accept_17_12_5_8_1_7680 29 107 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 107 161 (accept_3_2 28 107 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 107 161 (Polychromatic418967fa.accept_13_1_3_5_1_140 27 107 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 107 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 107 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 107 161 (accept_3_2 25 107 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 107 161 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 107 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 107 161
  (Polychromatic418967fa.accept_24_23_11_17_1_8885 23 107 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 107 161 (accept_3_2 22 107 161 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 107 161 (Polychromatic418967fa.accept_13_8_3_5_1_1636 21 107 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 107 161 (Polychromatic418967fa.accept_15_5_2_11_1_1596 20 107
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 107 161 (accept_3_2 19 107
  161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 107 161 (Polychromatic418967fa.accept_4_2_3_1_1_2
  18 107 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 107 161
  (Polychromatic418967fa.accept_21_17_2_14_1_7208 17 107 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 107 161 (accept_3_2 16 107 161 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 107 161 (Polychromatic418967fa.accept_11_4_8_7_1_819 15 107 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 107 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 107 161 (accept_3_2 13 107 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 107 161
  (Polychromatic418967fa.accept_14_12_9_7_1_2762 12 107 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 107 161 (Polychromatic418967fa.accept_13_11_3_5_1_982 11 107 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 161 (accept_3_2 10 107 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 107 161 (Polychromatic418967fa.accept_13_9_3_5_1_1605 9 107 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 161 (Polychromatic418967fa.accept_13_8_3_5_1_1636
  8 107 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 107 161 (accept_3_2 7
  107 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 107 161
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 107 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 107 161 (Polychromatic418967fa.accept_14_5_9_7_1_590 5 107 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 161 (accept_3_2 4 107 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 107 161 (Polychromatic418967fa.accept_17_3_5_8_1_1687 3 107 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 2
  107 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 107 161 (accept_3_2 1 107
  161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107 161)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 56 106 161 (Eq.refl Bool.true) (allA_of_3_0 56 106 161 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 57 105 161 (Eq.refl Bool.true) (allA_succ_of_gcd 56 105 161 7 8 15 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 105 161 (accept_3_2 55 105 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 105 161 (Polychromatic418967fa.accept_10_4_5_1_1_497 54 105
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 105 161
  (Polychromatic418967fa.accept_16_5_9_1_1_2070 53 105 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 105 161 (accept_3_2 52 105 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 105 161 (Polychromatic418967fa.accept_12_3_9_5_1_853 51 105 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 105 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 105 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 105 161 7 7 15 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 105 161
  (Polychromatic418967fa.accept_9_3_6_8_1_308 48 105 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 105 161 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 105 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 105 161 (accept_3_2 46 105 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 105 161 (Polychromatic418967fa.accept_11_1_6_7_1_116 45 105 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 105 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 105 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 105 161 (accept_3_2 43 105 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42
  105 161 7 6 15 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 105 161 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 105 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 105 161 (accept_3_2 40 105 161 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 105 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 105 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 105 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 105 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 161 (accept_3_2 37 105 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 105 161 (Polychromatic418967fa.accept_10_6_5_1_1_482
  36 105 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 105 161 7 5 15 23
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 105 161
  (accept_3_2 34 105 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 105 161
  (Polychromatic418967fa.accept_22_11_17_7_1_5448 33 105 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 105 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 105 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 161 (accept_3_2 31 105 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 105 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 105 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 105 161
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 105 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 105 161 7 4 15 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 105 161 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 105 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 105 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 161 (accept_3_2 25 105 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 105 161 (Polychromatic418967fa.accept_10_4_5_1_1_497
  24 105 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 105 161
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 105 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 105 161 (accept_3_2 22 105 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21
  105 161 7 3 15 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  20 105 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 105 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 105 161 (accept_3_2 19 105 161 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 105 161 (Polychromatic418967fa.accept_16_2_9_1_1_6404 18 105 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 161 (Polychromatic418967fa.accept_13_4_1_5_1_1628 17 105
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 161 (accept_3_2 16 105
  161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 105 161
  (Polychromatic418967fa.accept_12_3_9_5_1_853 15 105 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 105 161 7 2 15 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 105 161 (accept_3_2 13 105 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 105 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 105 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 105 161 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 105 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 105 161 (accept_3_2 10 105 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 105 161 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 105 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 105 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 105 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 105 161 7 1 15 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 105 161 (Polychromatic418967fa.accept_10_6_5_1_1_482 6 105 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 105 161 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 105 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 161 (accept_3_2 4 105 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 3
  105 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 105 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 105 161 (accept_3_2 1 105 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  161))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 104 161 (Eq.refl Bool.true)
  (allA_succ_of_accept 57 104 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 104 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 104 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 104 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 104 161 (accept_3_2 55 104 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 104 161
  (Polychromatic418967fa.accept_22_10_16_7_1_2608 54 104 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 104 161 (Polychromatic418967fa.accept_11_9_5_7_1_815 53 104 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 104 161 (accept_3_2 52 104 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 104 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 104 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 104 161
  (Polychromatic418967fa.accept_12_2_8_5_1_408 50 104 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 104 161 (accept_3_2 49 104 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 104 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 104 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 104 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 104 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 104 161 (accept_3_2 46 104 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 104 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 104 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 104 161
  (Polychromatic418967fa.accept_16_12_8_1_1_5270 44 104 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 104 161 (accept_3_2 43 104 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 104 161 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 104 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 104 161 (Polychromatic418967fa.accept_14_13_6_7_1_2013 41 104 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 104 161 (accept_3_2 40 104 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 104 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 104 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 104 161
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 104 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 104 161 (accept_3_2 37 104 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 104 161 (Polychromatic418967fa.accept_14_8_6_7_1_1934 36 104 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 104 161 (Polychromatic418967fa.accept_10_5_4_1_1_842 35 104 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 104 161 (accept_3_2 34 104 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 104 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 104 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 104 161
  (Polychromatic418967fa.accept_21_11_20_14_1_4179 32 104 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 104 161 (accept_3_2 31 104 161 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 104 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 104 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 104 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 104 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 104 161 (accept_3_2 28 104 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 104 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 27
  104 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 104 161
  (Polychromatic418967fa.accept_12_2_8_5_1_408 26 104 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 104 161 (accept_3_2 25 104 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 104 161 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 104 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 104 161 (Polychromatic418967fa.accept_16_7_8_1_1_3061 23 104 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 104 161 (accept_3_2 22 104 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 104 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 104 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 104 161
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 104 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 104 161 (accept_3_2 19 104 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 104 161 (Polychromatic418967fa.accept_15_3_14_11_1_1579 18 104 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 104 161 (Polychromatic418967fa.accept_10_7_4_1_1_1319 17 104 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 104 161 (accept_3_2 16 104 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 104 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 104 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 104 161
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 104 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 104 161 (accept_3_2 13 104 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 104 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 104 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 104 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 104 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 104 161 (accept_3_2 10 104 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 104 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 104 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 104 161
  (Polychromatic418967fa.accept_14_8_6_7_1_1934 8 104 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 104 161 (accept_3_2 7 104 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  104 161 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 104 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 104 161 (Polychromatic418967fa.accept_10_5_4_1_1_842 5 104 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 104 161 (accept_3_2 4 104 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 104 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 104 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 104 161
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 104 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 104 161 (accept_3_2 1 104 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  161)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 103 161 (Eq.refl Bool.true) (allA_of_3_0
  59 103 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 102 161 (Eq.refl Bool.true) (allA_succ_of_accept 59
  102 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 102 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 102 161 (accept_3_2 58 102 161 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 102 161 (Polychromatic418967fa.accept_21_15_18_14_1_5632 57 102 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 102 161 (Polychromatic418967fa.accept_9_2_3_8_1_318
  56 102 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 102 161 (accept_3_2 55
  102 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 102 161
  (Polychromatic418967fa.accept_11_10_3_7_1_2564 54 102 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 102 161 (Polychromatic418967fa.accept_10_3_2_1_1_839 53 102 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 102 161 (accept_3_2 52 102 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 102 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 102 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 102 161 (Polychromatic418967fa.accept_9_5_3_8_1_316
  50 102 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 102 161 (accept_3_2 49
  102 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 102 161
  (Polychromatic418967fa.accept_11_4_3_7_1_828 48 102 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 102 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 102 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 102 161 (accept_3_2 46 102 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 102 161 (Polychromatic418967fa.accept_13_6_11_5_1_133 45 102 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 102 161
  (Polychromatic418967fa.accept_15_14_12_11_1_1572 44 102 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 102 161 (accept_3_2 43 102 161 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 102 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 102 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 102 161 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 102 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 102 161 (accept_3_2 40 102 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 102 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 39
  102 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 102 161
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 102 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 102 161 (accept_3_2 37 102 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 102 161 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 102 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 102 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 102 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 102 161 (accept_3_2 34 102 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 102 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 102 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 102 161
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 102 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 102 161 (accept_3_2 31 102 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 102 161 (Polychromatic418967fa.accept_19_11_7_9_1_8873 30 102 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 102 161 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 102 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 102 161 (accept_3_2 28 102 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 102 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 102 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 102 161
  (Polychromatic418967fa.accept_10_6_2_1_1_494 26 102 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 102 161 (accept_3_2 25 102 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 102 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 102 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 102 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 102 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 102 161 (accept_3_2 22 102 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 102 161 (Polychromatic418967fa.accept_11_10_3_7_1_2564 21 102 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 102 161
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 102 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 102 161 (accept_3_2 19 102 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 102 161 (Polychromatic418967fa.accept_16_2_6_1_1_2069 18 102 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 102 161 (Polychromatic418967fa.accept_14_3_4_7_1_175 17 102 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 102 161 (accept_3_2 16 102 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 102 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 102 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 102 161
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 102 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 102 161 (accept_3_2 13 102 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 102 161 (Polychromatic418967fa.accept_21_12_18_14_1_8854 12 102 161 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 11 102 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 102 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 102 161 (accept_3_2 10 102 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 102 161 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 102 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 102 161
  (Polychromatic418967fa.accept_15_8_12_11_1_1570 8 102 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 102 161 (accept_3_2 7 102 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  102 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 102 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 102 161 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 102 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 102 161 (accept_3_2 4 102 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 102 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 102 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 102 161
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 102 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 102 161 (accept_3_2 1 102 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  161)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 101 161 (Eq.refl Bool.true)
  (allA_succ_of_accept 60 101 161 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 101 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 101 161 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 101 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 101 161 (accept_3_2 58 101 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 101 161 (Polychromatic418967fa.accept_9_3_2_8_1_108
  57 101 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 101 161
  (Polychromatic418967fa.accept_13_4_10_5_1_1644 56 101 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 101 161 (accept_3_2 55 101 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 101 161 (Polychromatic418967fa.accept_13_2_10_5_1_1643 54 101 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 101 161 (Polychromatic418967fa.accept_11_9_2_7_1_1298 53 101 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 101 161 (accept_3_2 52 101 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 101 161 (Polychromatic418967fa.accept_9_6_2_8_1_592 51 101 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 101 161
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 101 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 101 161 (accept_3_2 49 101 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 101 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 101 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 101 161 (Polychromatic418967fa.accept_13_8_10_5_1_977 47 101 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 101 161 (accept_3_2 46 101 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 101 161 (Polychromatic418967fa.accept_13_6_10_5_1_1648 45 101
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 101 161
  (Polychromatic418967fa.accept_8_4_5_1_1_299 44 101 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 101 161 (accept_3_2 43 101 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 101 161 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 101 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 101 161 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 101 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 101 161 (accept_3_2 40 101 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 101 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 101 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 101 161
  (Polychromatic418967fa.accept_14_10_3_7_1_1975 38 101 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 101 161 (accept_3_2 37 101 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 101 161 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 101 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 101 161 (Polychromatic418967fa.accept_19_16_6_9_1_7335 35 101 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 101 161 (accept_3_2 34 101 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 101 161 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 101 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 101 161
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 101 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 101 161 (accept_3_2 31 101 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 101 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 101 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 101 161 (Polychromatic418967fa.accept_16_13_5_1_1_3017 29 101 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 101 161 (accept_3_2 28 101 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 101 161 (Polychromatic418967fa.accept_26_1_23_5_1_8884 27 101
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 101 161
  (Polychromatic418967fa.accept_17_9_16_8_1_2721 26 101 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 101 161 (accept_3_2 25 101 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 101 161 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 101 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 101 161 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 101 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 101 161 (accept_3_2 22 101 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 101 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 101 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 101 161
  (Polychromatic418967fa.accept_8_4_5_1_1_299 20 101 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 101 161 (accept_3_2 19 101 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 101 161 (Polychromatic418967fa.accept_14_4_3_7_1_3702 18 101 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 101 161 (Polychromatic418967fa.accept_13_4_10_5_1_1644 17 101 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 161 (accept_3_2 16 101 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 101 161 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 101 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 101 161
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 101 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 101 161 (accept_3_2 13 101 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 101 161 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 101 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 101 161 (Polychromatic418967fa.accept_14_11_3_7_1_604 11 101 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 161 (accept_3_2 10 101 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 101 161 (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 101 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 161
  (Polychromatic418967fa.accept_13_8_10_5_1_977 8 101 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 101 161 (accept_3_2 7 101 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  101 161 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 101 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 101 161 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 101 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 161 (accept_3_2 4 101 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 101 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 161
  (Polychromatic418967fa.accept_13_2_10_5_1_1643 2 101 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 101 161 (accept_3_2 1 101 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101
  161))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 100 161 (Eq.refl Bool.true)
  (allA_of_3_0 62 100 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 63 99 161 (Eq.refl Bool.true)
  (allA_succ_of_accept 62 99 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 99 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 99 161 (accept_3_2 61 99 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 99 161 (Polychromatic418967fa.accept_21_18_15_14_1_8871 60 99 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 99 161
  (Polychromatic418967fa.accept_19_2_4_9_1_1131 59 99 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 99 161 (accept_3_2 58 99 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  99 161 (Polychromatic418967fa.accept_12_9_3_5_1_423 57 99 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 99 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 99 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 99 161 (accept_3_2 55 99 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 99 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 99 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 99 161
  (Polychromatic418967fa.accept_13_1_8_5_1_2315 53 99 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 99 161 (accept_3_2 52 99 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  99 161 (Polychromatic418967fa.accept_13_12_8_5_1_976 51 99 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 99 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 99 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 99 161 (accept_3_2 49 99 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 99 161 (Polychromatic418967fa.accept_10_8_9_1_1_189 48 99 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 99 161
  (Polychromatic418967fa.accept_15_2_9_11_1_1551 47 99 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 99 161 (accept_3_2 46 99 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  99 161 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 99 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 99 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 99 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 99 161 (accept_3_2 43 99 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 99 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 99 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 99 161
  (Polychromatic418967fa.accept_14_13_1_7_1_1211 41 99 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 99 161 (accept_3_2 40 99 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  99 161 (Polychromatic418967fa.accept_21_18_15_14_1_8871 39 99 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 99 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 99 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 99 161 (accept_3_2 37 99 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 99 161 (Polychromatic418967fa.accept_13_10_8_5_1_1616 36 99 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 99 161
  (Polychromatic418967fa.accept_10_5_9_1_1_187 35 99 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 99 161 (accept_3_2 34 99 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  99 161 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 99 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 99 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 99 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 161 (accept_3_2 31 99 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 99 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 99 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 161
  (Polychromatic418967fa.accept_13_3_8_5_1_974 29 99 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 99 161 (accept_3_2 28 99 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  99 161 (Polychromatic418967fa.accept_13_1_8_5_1_2315 27 99 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 99 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 99 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 161 (accept_3_2 25 99 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 99 161 (Polychromatic418967fa.accept_17_7_14_8_1_5069 24 99 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 99 161
  (Polychromatic418967fa.accept_13_10_8_5_1_1616 23 99 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 99 161 (accept_3_2 22 99 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  99 161 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 99 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 99 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 99 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 99 161 (accept_3_2 19 99 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 99 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 99 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 161
  (Polychromatic418967fa.accept_15_2_9_11_1_1551 17 99 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 99 161 (accept_3_2 16 99 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  99 161 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 99 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 99 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 99 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 161 (accept_3_2 13 99 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 99 161 (Polychromatic418967fa.accept_10_2_9_1_1_185 12 99 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 99 161
  (Polychromatic418967fa.accept_17_11_14_8_1_2729 11 99 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 99 161 (accept_3_2 10 99 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  99 161 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 99 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 99 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 99 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 161 (accept_3_2 7 99 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 99 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 99 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 161
  (Polychromatic418967fa.accept_10_5_9_1_1_187 5 99 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 99 161 (accept_3_2 4 99 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99
  161 (Polychromatic418967fa.accept_13_3_8_5_1_974 3 99 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 99 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 99 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 161 (accept_3_2 1 99 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 99 161))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 98 161
  (Eq.refl Bool.true) (allA_succ_of_gcd 63 98 161 7 9 14 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 62 98 161 (Polychromatic418967fa.accept_25_12_23_11_1_8883 62 98 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 98 161 (accept_3_2 61 98 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 98 161 (Polychromatic418967fa.accept_16_12_2_1_1_1215 60 98
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 98 161
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 98 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 98 161 (accept_3_2 58 98 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  98 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 98 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 98 161 7 8 14 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 98 161 (accept_3_2 55 98 161 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 98 161 (Polychromatic418967fa.accept_13_2_7_5_1_3189 54 98 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 98 161 (Polychromatic418967fa.accept_10_3_8_1_1_182 53 98 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 98 161 (accept_3_2 52 98 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 98 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 51
  98 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 98 161
  (Polychromatic418967fa.accept_13_11_7_5_1_2314 50 98 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 49 98 161 7 7 14 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 48 98 161 (Polychromatic418967fa.accept_15_3_8_11_1_4386 48 98 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 98 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 98 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 98 161 (accept_3_2 46 98 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 98 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 45
  98 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 98 161
  (Polychromatic418967fa.accept_12_8_2_5_1_844 44 98 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 98 161 (accept_3_2 43 98 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 98
  161 7 6 14 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  98 161 (Polychromatic418967fa.accept_13_2_7_5_1_3189 41 98 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 98 161 (accept_3_2 40 98 161 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 98 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 98 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 98 161 (Polychromatic418967fa.accept_13_12_7_5_1_3147 38 98
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 98 161 (accept_3_2 37 98 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 98 161 (Polychromatic418967fa.accept_11_3_10_7_1_129
  36 98 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 98 161 7 5 14 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 98 161 (accept_3_2 34
  98 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 98 161
  (Polychromatic418967fa.accept_6_3_2_5_1_32 33 98 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 98 161 (Polychromatic418967fa.accept_12_8_2_5_1_844 32 98 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 98 161 (accept_3_2 31 98 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 98 161 (Polychromatic418967fa.accept_19_11_3_9_1_8882 30 98 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 98 161
  (Polychromatic418967fa.accept_10_9_8_1_1_1331 29 98 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 98 161 7 4 14 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 98 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 98 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 98 161 (Polychromatic418967fa.accept_22_4_10_7_1_8881 26 98
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 98 161 (accept_3_2 25 98 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 98 161 (Polychromatic418967fa.accept_13_11_7_5_1_2314
  24 98 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 98 161
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 98 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 98 161 (accept_3_2 22 98 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 98
  161 7 3 14 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20
  98 161 (Polychromatic418967fa.accept_12_8_2_5_1_844 20 98 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 98 161 (accept_3_2 19 98 161 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 98 161 (Polychromatic418967fa.accept_15_3_8_11_1_4386 18 98 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 98 161 (Polychromatic418967fa.accept_20_17_18_1_1_8880 17 98
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 98 161 (accept_3_2 16 98 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 98 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 15
  98 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 98 161 7 2 14 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 98 161 (accept_3_2 13
  98 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 98 161
  (Polychromatic418967fa.accept_13_12_7_5_1_3147 12 98 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 98 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 98 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 98 161 (accept_3_2 10 98 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 98 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 98 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 98 161 (Polychromatic418967fa.accept_12_8_2_5_1_844 8
  98 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 98 161 7 1 14 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 98 161
  (Polychromatic418967fa.accept_16_6_2_1_1_4081 6 98 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 98 161 (Polychromatic418967fa.accept_15_5_8_11_1_2350 5 98 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 98 161 (accept_3_2 4 98 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 98 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 98 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 98 161 (Polychromatic418967fa.accept_13_2_7_5_1_3189 2
  98 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 98 161 (accept_3_2 1 98 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  161)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 97 161 (Eq.refl Bool.true)
  (allA_of_3_0 65 97 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 66 96 161 (Eq.refl Bool.true)
  (allA_succ_of_accept 65 96 161 (Polychromatic418967fa.accept_9_2_6_8_1_321 65 96 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 96 161 (accept_3_2 64 96 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 96 161 (Polychromatic418967fa.accept_15_3_6_11_1_855 63 96 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 96 161 (Polychromatic418967fa.accept_10_2_6_1_1_1296
  62 96 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 96 161 (accept_3_2 61
  96 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 96 161
  (Polychromatic418967fa.accept_17_9_11_8_1_5077 60 96 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 96 161 (Polychromatic418967fa.accept_9_5_6_8_1_101 59 96 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 96 161 (accept_3_2 58 96 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 96 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 96 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 96 161 (Polychromatic418967fa.accept_9_2_6_8_1_321 56
  96 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 96 161 (accept_3_2 55 96
  161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 96 161
  (Polychromatic418967fa.accept_15_9_6_11_1_1586 54 96 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 96 161 (Polychromatic418967fa.accept_17_2_11_8_1_2726 53 96 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 96 161 (accept_3_2 52 96 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 96 161 (Polychromatic418967fa.accept_14_9_12_7_1_597 51 96 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 96 161 (Polychromatic418967fa.accept_9_5_6_8_1_101 50
  96 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 96 161 (accept_3_2 49 96
  161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 96 161
  (Polychromatic418967fa.accept_9_3_6_8_1_308 48 96 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 96 161 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 96 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 96 161 (accept_3_2 46 96 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 96 161 (Polychromatic418967fa.accept_10_5_6_1_1_836 45 96 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 96 161 (Polychromatic418967fa.accept_14_2_12_7_1_617
  44 96 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 96 161 (accept_3_2 43
  96 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 96 161
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 96 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 96 161 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 96 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 96 161 (accept_3_2 40 96 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 96 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 96 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 96 161 (Polychromatic418967fa.accept_9_2_6_8_1_321 38
  96 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 96 161 (accept_3_2 37 96
  161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 96 161
  (Polychromatic418967fa.accept_17_2_11_8_1_2726 36 96 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 96 161 (Polychromatic418967fa.accept_10_5_6_1_1_836 35 96 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 96 161 (accept_3_2 34 96 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 96 161 (Polychromatic418967fa.accept_14_5_12_7_1_2767 33 96 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 96 161
  (Polychromatic418967fa.accept_9_5_6_8_1_101 32 96 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 96 161 (accept_3_2 31 96 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  96 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 96 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 96 161 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 96 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 96 161 (accept_3_2 28 96 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 96 161 (Polychromatic418967fa.accept_10_7_6_1_1_486 27 96 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 96 161
  (Polychromatic418967fa.accept_11_4_8_7_1_819 26 96 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 96 161 (accept_3_2 25 96 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  96 161 (Polychromatic418967fa.accept_15_9_6_11_1_1586 24 96 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 96 161 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 96 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 96 161 (accept_3_2 22 96 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 96 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 96 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 96 161
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 96 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 96 161 (accept_3_2 19 96 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  96 161 (Polychromatic418967fa.accept_15_3_6_11_1_855 18 96 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 96 161 (Polychromatic418967fa.accept_10_7_6_1_1_486 17 96 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 96 161 (accept_3_2 16 96 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 96 161 (Polychromatic418967fa.accept_10_5_6_1_1_836 15 96 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 96 161
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 96 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 96 161 (accept_3_2 13 96 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  96 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 96 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 96 161 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 96 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 96 161 (accept_3_2 10 96 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 96 161 (Polychromatic418967fa.accept_14_9_12_7_1_597 9 96 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 96 161
  (Polychromatic418967fa.accept_19_8_1_9_1_7329 8 96 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 96 161 (accept_3_2 7 96 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 96
  161 (Polychromatic418967fa.accept_20_6_16_1_1_7262 6 96 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 96 161 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 96 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 96 161 (accept_3_2 4 96 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 96 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 96 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 96 161
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 96 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 96 161 (accept_3_2 1 96 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  161)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 95 161 (Eq.refl Bool.true)
  (allA_succ_of_accept 66 95 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 95 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 95 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 95 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 95 161 (accept_3_2 64 95 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 95 161
  (Polychromatic418967fa.accept_17_12_10_8_1_5039 63 95 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 95 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 95 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 161 (accept_3_2 61 95 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 95 161 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 95 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 95 161 (Polychromatic418967fa.accept_10_9_5_1_1_1325
  59 95 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 95 161 (accept_3_2 58
  95 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 95 161
  (Polychromatic418967fa.accept_9_3_5_8_1_99 57 95 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 95 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 95 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 95 161 (accept_3_2 55 95 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 95 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 95 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 161 (Polychromatic418967fa.accept_13_1_4_5_1_113
  53 95 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 95 161 (accept_3_2 52
  95 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 95 161
  (Polychromatic418967fa.accept_9_6_5_8_1_598 51 95 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 95 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 95 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 95 161 (accept_3_2 49 95 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 95 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 95 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 95 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 47
  95 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 95 161 (accept_3_2 46 95
  161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 95 161
  (Polychromatic418967fa.accept_13_6_4_5_1_2330 45 95 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 95 161 (Polychromatic418967fa.accept_10_4_5_1_1_497 44 95 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 161 (accept_3_2 43 95 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 95 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 95 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 161 (Polychromatic418967fa.accept_13_2_4_5_1_3152
  41 95 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 95 161 (accept_3_2 40
  95 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 95 161
  (Polychromatic418967fa.accept_9_3_5_8_1_99 39 95 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 95 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 95 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 161 (accept_3_2 37 95 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 95 161 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 95 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 95 161 (Polychromatic418967fa.accept_13_9_4_5_1_1651
  35 95 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 95 161 (accept_3_2 34
  95 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 95 161
  (Polychromatic418967fa.accept_9_6_5_8_1_598 33 95 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 95 161 (Polychromatic418967fa.accept_13_6_4_5_1_2330 32 95 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 161 (accept_3_2 31 95 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 95 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 95 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 95 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 29
  95 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 95 161 (accept_3_2 28 95
  161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 95 161
  (Polychromatic418967fa.accept_13_1_4_5_1_113 27 95 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 95 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 95 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 161 (accept_3_2 25 95 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 95 161 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 95 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 161 (Polychromatic418967fa.accept_13_10_4_5_1_2331
  23 95 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 95 161 (accept_3_2 22
  95 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 95 161
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 95 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 95 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 95 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 161 (accept_3_2 19 95 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 95 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 95 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 161 (Polychromatic418967fa.accept_14_3_11_7_1_1260
  17 95 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 95 161 (accept_3_2 16
  95 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 95 161
  (Polychromatic418967fa.accept_9_6_5_8_1_598 15 95 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 95 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 95 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 161 (accept_3_2 13 95 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 95 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 95 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 11
  95 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 95 161 (accept_3_2 10 95
  161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 95 161
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 95 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 95 161 (Polychromatic418967fa.accept_15_8_5_11_1_2358 8 95 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 161 (accept_3_2 7 95 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 95 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 95 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 161 (Polychromatic418967fa.accept_16_5_15_1_1_2113
  5 95 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 95 161 (accept_3_2 4 95
  161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95 161 (Polychromatic418967fa.accept_9_3_5_8_1_99
  3 95 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 95 161
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 95 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 95 161 (accept_3_2 1 95 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 95
  161))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 94 161 (Eq.refl Bool.true)
  (allA_of_3_0 68 94 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 69 93 161 (Eq.refl Bool.true)
  (allA_succ_of_accept 68 93 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 93 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 93 161 (accept_3_2 67 93 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 93 161 (Polychromatic418967fa.accept_15_6_3_11_1_848 66 93 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 93 161 (Polychromatic418967fa.accept_9_2_3_8_1_318 65
  93 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 161 (accept_3_2 64 93
  161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 93 161
  (Polychromatic418967fa.accept_12_3_9_5_1_853 63 93 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 93 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 93 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 93 161 (accept_3_2 61 93 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 93 161 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 93 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 93 161 (Polychromatic418967fa.accept_9_5_3_8_1_316 59
  93 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 161 (accept_3_2 58 93
  161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 93 161
  (Polychromatic418967fa.accept_16_9_13_1_1_3069 57 93 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 93 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 93 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 93 161 (accept_3_2 55 93 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 93 161 (Polychromatic418967fa.accept_14_12_9_7_1_2762 54 93 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 93 161
  (Polychromatic418967fa.accept_11_9_5_7_1_815 53 93 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 93 161 (accept_3_2 52 93 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  93 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 93 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 93 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 93 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 93 161 (accept_3_2 49 93 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 93 161 (Polychromatic418967fa.accept_10_8_3_1_1_1316 48 93 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 93 161
  (Polychromatic418967fa.accept_9_2_3_8_1_318 47 93 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 93 161 (accept_3_2 46 93 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  93 161 (Polychromatic418967fa.accept_19_7_17_9_1_8879 45 93 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 93 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 93 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 93 161 (accept_3_2 43 93 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 93 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 93 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 93 161
  (Polychromatic418967fa.accept_9_5_3_8_1_316 41 93 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 93 161 (accept_3_2 40 93 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  93 161 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 93 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 93 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 93 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 93 161 (accept_3_2 37 93 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 93 161 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 93 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 93 161
  (Polychromatic418967fa.accept_13_9_2_5_1_2310 35 93 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 93 161 (accept_3_2 34 93 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  93 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 93 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 93 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 93 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 93 161 (accept_3_2 31 93 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 93 161 (Polychromatic418967fa.accept_13_4_2_5_1_4045 30 93 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 93 161
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 93 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 93 161 (accept_3_2 28 93 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  93 161 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 93 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 93 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 93 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 93 161 (accept_3_2 25 93 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 93 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 93 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 93 161
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 93 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 93 161 (accept_3_2 22 93 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  93 161 (Polychromatic418967fa.accept_15_6_3_11_1_848 21 93 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 93 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 93 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 161 (accept_3_2 19 93 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 93 161 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 93 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 161
  (Polychromatic418967fa.accept_13_4_2_5_1_4045 17 93 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 93 161 (accept_3_2 16 93 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  93 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 93 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 93 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 93 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 161 (accept_3_2 13 93 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 93 161 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 93 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 161
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 93 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 93 161 (accept_3_2 10 93 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  93 161 (Polychromatic418967fa.accept_11_9_5_7_1_815 9 93 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 93 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 93 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 161 (accept_3_2 7 93 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 93 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 93 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 161
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 93 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 93 161 (accept_3_2 4 93 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93
  161 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 93 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 93 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 93 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 161 (accept_3_2 1 93 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 93 161))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 92
  161 (Eq.refl Bool.true) (allA_succ_of_gcd 69 92 161 23 3 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 92 161 (Polychromatic418967fa.accept_9_5_2_8_1_109 68 92 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 92 161 (accept_3_2 67 92 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 92 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 66
  92 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 92 161
  (Polychromatic418967fa.accept_15_5_2_11_1_1596 65 92 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 92 161 (accept_3_2 64 92 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  92 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 92 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 92 161 (Polychromatic418967fa.accept_12_2_8_5_1_408 62 92 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 92 161 (accept_3_2 61 92 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 92 161 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 92 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 92 161
  (Polychromatic418967fa.accept_9_5_2_8_1_109 59 92 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 92 161 (accept_3_2 58 92 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  92 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 92 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 92 161 (Polychromatic418967fa.accept_10_6_2_1_1_494 56 92 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 92 161 (accept_3_2 55 92 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 92 161 (Polychromatic418967fa.accept_15_9_2_11_1_2391 54 92 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 92 161
  (Polychromatic418967fa.accept_8_5_4_1_1_111 53 92 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 92 161 (accept_3_2 52 92 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  92 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 92 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 92 161 (Polychromatic418967fa.accept_9_5_2_8_1_109 50 92 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 92 161 (accept_3_2 49 92 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 92 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 92 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 92 161
  (Polychromatic418967fa.accept_11_3_4_7_1_114 47 92 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 92 161 23 2 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 92 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 92 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 92 161 (Polychromatic418967fa.accept_18_8_2_17_1_4782 44 92
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 92 161 (accept_3_2 43 92 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 92 161 (Polychromatic418967fa.accept_9_6_2_8_1_592 42
  92 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 92 161
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 92 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 92 161 (accept_3_2 40 92 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  92 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 92 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 92 161 (Polychromatic418967fa.accept_12_2_8_5_1_408 38 92 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 92 161 (accept_3_2 37 92 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 92 161 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 92 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 92 161
  (Polychromatic418967fa.accept_13_9_1_5_1_964 35 92 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 92 161 (accept_3_2 34 92 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  92 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 92 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 92 161 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 92 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 92 161 (accept_3_2 31 92 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 92 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 92 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 92 161
  (Polychromatic418967fa.accept_8_5_4_1_1_111 29 92 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 92 161 (accept_3_2 28 92 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  92 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 92 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 92 161 (Polychromatic418967fa.accept_10_6_2_1_1_494 26 92 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 92 161 (accept_3_2 25 92 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 92 161 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 92 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 23 92 161 23 1 4 7 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 22 92 161 (accept_3_2 22 92 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 92 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 92 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 92 161
  (Polychromatic418967fa.accept_14_6_8_7_1_589 20 92 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 92 161 (accept_3_2 19 92 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  92 161 (Polychromatic418967fa.accept_16_2_12_1_1_3086 18 92 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 92 161 (Polychromatic418967fa.accept_13_4_1_5_1_1628 17 92 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 92 161 (accept_3_2 16 92 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 92 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 92 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 92 161
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 92 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 92 161 (accept_3_2 13 92 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  92 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 92 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 92 161 (Polychromatic418967fa.accept_16_11_12_1_1_3001 11 92 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 92 161 (accept_3_2 10 92 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 92 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 92 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 92 161
  (Polychromatic418967fa.accept_11_8_4_7_1_1303 8 92 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 92 161 (accept_3_2 7 92 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 92
  161 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 92 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 92 161 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 92 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 92 161 (accept_3_2 4 92 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 92 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 92 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 92 161 (Polychromatic418967fa.accept_12_2_8_5_1_408 2
  92 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 161 (accept_3_2 1 92 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  161)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 91 161 (Eq.refl Bool.true)
  (allA_of_3_0 71 91 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 72 90 161 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 90 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 90 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 90 161 (accept_3_2 70 90 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 90 161 (Polychromatic418967fa.accept_13_4_12_5_1_476 69 90 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 90 161
  (Polychromatic418967fa.accept_19_11_14_9_1_4599 68 90 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 90 161 (accept_3_2 67 90 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  90 161 (Polychromatic418967fa.accept_13_1_12_5_1_1601 66 90 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 90 161 (Polychromatic418967fa.accept_19_8_14_9_1_4590 65 90 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 90 161 (accept_3_2 64 90 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 90 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 90 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 90 161
  (Polychromatic418967fa.accept_19_5_14_9_1_4554 62 90 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 90 161 (accept_3_2 61 90 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  90 161 (Polychromatic418967fa.accept_13_8_12_5_1_1604 60 90 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 90 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 90 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 90 161 (accept_3_2 58 90 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 90 161 (Polychromatic418967fa.accept_14_1_6_7_1_1936 57 90 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 90 161
  (Polychromatic418967fa.accept_13_4_12_5_1_476 56 90 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 90 161 (accept_3_2 55 90 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  90 161 (Polychromatic418967fa.accept_13_2_12_5_1_1602 54 90 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 90 161 (Polychromatic418967fa.accept_11_9_2_7_1_1298 53 90 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 90 161 (accept_3_2 52 90 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 90 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 90 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 90 161
  (Polychromatic418967fa.accept_14_8_6_7_1_1934 50 90 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 90 161 (accept_3_2 49 90 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  90 161 (Polychromatic418967fa.accept_27_21_9_26_1_8878 48 90 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 90 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 90 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 90 161 (accept_3_2 46 90 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 90 161 (Polychromatic418967fa.accept_13_6_12_5_1_2304 45 90 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 90 161
  (Polychromatic418967fa.accept_19_6_14_9_1_8863 44 90 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 90 161 (accept_3_2 43 90 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  90 161 (Polychromatic418967fa.accept_11_9_2_7_1_1298 42 90 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 90 161 (Polychromatic418967fa.accept_13_2_12_5_1_1602 41 90 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 90 161 (accept_3_2 40 90 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 90 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 90 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 90 161
  (Polychromatic418967fa.accept_25_13_15_11_1_8877 38 90 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 90 161 (accept_3_2 37 90 161 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 90 161 (Polychromatic418967fa.accept_14_8_6_7_1_1934 36 90 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 90 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 90 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 90 161 (accept_3_2 34 90 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 90 161 (Polychromatic418967fa.accept_13_7_12_5_1_1603
  33 90 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 90 161
  (Polychromatic418967fa.accept_13_6_12_5_1_2304 32 90 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 90 161 (accept_3_2 31 90 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  90 161 (Polychromatic418967fa.accept_13_4_12_5_1_476 30 90 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 90 161 (Polychromatic418967fa.accept_14_1_6_7_1_1936 29 90 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 90 161 (accept_3_2 28 90 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 90 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 90 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 90 161
  (Polychromatic418967fa.accept_25_1_15_11_1_6999 26 90 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 90 161 (accept_3_2 25 90 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  90 161 (Polychromatic418967fa.accept_19_5_14_9_1_4554 24 90 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 90 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 90 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 90 161 (accept_3_2 22 90 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 90 161 (Polychromatic418967fa.accept_13_8_12_5_1_1604 21 90 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 90 161
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 20 90 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 90 161 (accept_3_2 19 90 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  90 161 (Polychromatic418967fa.accept_21_18_6_14_1_2812 18 90 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 90 161 (Polychromatic418967fa.accept_13_4_12_5_1_476 17 90 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 90 161 (accept_3_2 16 90 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 90 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 90 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 90 161
  (Polychromatic418967fa.accept_13_1_12_5_1_1601 14 90 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 90 161 (accept_3_2 13 90 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  90 161 (Polychromatic418967fa.accept_17_12_5_8_1_7680 12 90 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 90 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 90 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 90 161 (accept_3_2 10 90 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 90 161 (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 90 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 90 161
  (Polychromatic418967fa.accept_13_8_12_5_1_1604 8 90 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 90 161 (accept_3_2 7 90 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 90
  161 (Polychromatic418967fa.accept_13_6_12_5_1_2304 6 90 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 90 161 (Polychromatic418967fa.accept_19_5_14_9_1_4554 5 90 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 90 161 (accept_3_2 4 90 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 90 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 90 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 90 161
  (Polychromatic418967fa.accept_13_2_12_5_1_1602 2 90 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 90 161 (accept_3_2 1 90 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  161)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 89 161 (Eq.refl Bool.true)
  (allA_succ_of_accept 72 89 161 (Polychromatic418967fa.accept_10_2_9_1_1_185 72 89 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 161 (Polychromatic418967fa.accept_13_6_11_5_1_133 71 89 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 89 161 (accept_3_2 70 89 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 89 161 (Polychromatic418967fa.accept_16_5_9_1_1_2070
  69 89 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 89 161
  (Polychromatic418967fa.accept_10_8_9_1_1_189 68 89 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 89 161 (accept_3_2 67 89 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  89 161 (Polychromatic418967fa.accept_16_2_9_1_1_6404 66 89 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 89 161 (Polychromatic418967fa.accept_10_5_9_1_1_187 65 89 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 89 161 (accept_3_2 64 89 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 89 161 (Polychromatic418967fa.accept_15_3_14_11_1_1579 63 89 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 89 161
  (Polychromatic418967fa.accept_10_2_9_1_1_185 62 89 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 89 161 (accept_3_2 61 89 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  89 161 (Polychromatic418967fa.accept_19_3_13_9_1_8876 60 89 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 89 161 (Polychromatic418967fa.accept_13_7_11_5_1_2302 59 89 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 89 161 (accept_3_2 58 89 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 89 161 (Polychromatic418967fa.accept_15_12_14_11_1_4375 57 89
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 89 161
  (Polychromatic418967fa.accept_16_8_9_1_1_7753 56 89 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 89 161 (accept_3_2 55 89 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  89 161 (Polychromatic418967fa.accept_14_12_5_7_1_2010 54 89 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 89 161 (Polychromatic418967fa.accept_16_5_9_1_1_2070 53 89 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 89 161 (accept_3_2 52 89 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 89 161 (Polychromatic418967fa.accept_14_9_5_7_1_1251 51 89 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 89 161
  (Polychromatic418967fa.accept_11_6_1_7_1_1315 50 89 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 89 161 (accept_3_2 49 89 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  89 161 (Polychromatic418967fa.accept_10_8_9_1_1_189 48 89 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 89 161 (Polychromatic418967fa.accept_17_13_4_8_1_3830 47 89 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 89 161 (accept_3_2 46 89 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 89 161 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 89 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 89 161
  (Polychromatic418967fa.accept_14_2_5_7_1_3767 44 89 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 89 161 (accept_3_2 43 89 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  89 161 (Polychromatic418967fa.accept_10_2_9_1_1_185 42 89 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 89 161 (Polychromatic418967fa.accept_17_7_4_8_1_7678 41 89 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 89 161 (accept_3_2 40 89 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 89 161 (Polychromatic418967fa.accept_11_6_1_7_1_1315 39 89 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 89 161
  (Polychromatic418967fa.accept_10_8_9_1_1_189 38 89 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 89 161 (accept_3_2 37 89 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  89 161 (Polychromatic418967fa.accept_19_17_13_9_1_5970 36 89 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 89 161 (Polychromatic418967fa.accept_10_5_9_1_1_187 35 89 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 89 161 (accept_3_2 34 89 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 89 161 (Polychromatic418967fa.accept_13_7_11_5_1_2302 33 89 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 89 161
  (Polychromatic418967fa.accept_10_2_9_1_1_185 32 89 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 89 161 (accept_3_2 31 89 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  89 161 (Polychromatic418967fa.accept_14_2_5_7_1_3767 30 89 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 89 161 (Polychromatic418967fa.accept_13_3_11_5_1_2348 29 89 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 89 161 (accept_3_2 28 89 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 89 161 (Polychromatic418967fa.accept_15_12_14_11_1_4375 27 89
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 89 161
  (Polychromatic418967fa.accept_14_12_5_7_1_2010 26 89 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 89 161 (accept_3_2 25 89 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  89 161 (Polychromatic418967fa.accept_16_8_9_1_1_7753 24 89 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 89 161 (Polychromatic418967fa.accept_14_9_5_7_1_1251 23 89 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 89 161 (accept_3_2 22 89 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 89 161 (Polychromatic418967fa.accept_16_5_9_1_1_2070 21 89 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 89 161
  (Polychromatic418967fa.accept_13_7_11_5_1_2302 20 89 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 89 161 (accept_3_2 19 89 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  89 161 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 89 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 89 161 (Polychromatic418967fa.accept_11_6_1_7_1_1315 17 89 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 89 161 (accept_3_2 16 89 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 89 161 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 89 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 89 161
  (Polychromatic418967fa.accept_27_14_8_26_1_6796 14 89 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 89 161 (accept_3_2 13 89 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  89 161 (Polychromatic418967fa.accept_10_2_9_1_1_185 12 89 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 89 161 (Polychromatic418967fa.accept_21_11_5_14_1_4142 11 89 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 89 161 (accept_3_2 10 89 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 89 161 (Polychromatic418967fa.accept_14_9_5_7_1_1251 9 89 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 89 161
  (Polychromatic418967fa.accept_10_8_9_1_1_189 8 89 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 89 161 (accept_3_2 7 89 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 89
  161 (Polychromatic418967fa.accept_11_6_1_7_1_1315 6 89 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 89 161 (Polychromatic418967fa.accept_10_5_9_1_1_187 5 89 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 89 161 (accept_3_2 4 89 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 89 161 (Polychromatic418967fa.accept_13_3_11_5_1_2348 3 89 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 89 161
  (Polychromatic418967fa.accept_10_2_9_1_1_185 2 89 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 89 161 (accept_3_2 1 89 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 89
  161))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 88 161 (Eq.refl Bool.true)
  (allA_of_3_0 74 88 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 75 87 161 (Eq.refl Bool.true)
  (allA_succ_of_accept 74 87 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 87 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 87 161 (accept_3_2 73 87 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 87 161 (Polychromatic418967fa.accept_16_8_7_1_1_8875 72 87 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 87 161
  (Polychromatic418967fa.accept_19_14_11_9_1_3330 71 87 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 87 161 (accept_3_2 70 87 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  87 161 (Polychromatic418967fa.accept_11_3_10_7_1_129 69 87 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 87 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 87 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 87 161 (accept_3_2 67 87 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 87 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 87 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 87 161
  (Polychromatic418967fa.accept_9_2_6_8_1_321 65 87 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 87 161 (accept_3_2 64 87 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  87 161 (Polychromatic418967fa.accept_18_9_15_17_1_3497 63 87 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 87 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 87 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 87 161 (accept_3_2 61 87 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 87 161 (Polychromatic418967fa.accept_14_4_3_7_1_3702 60 87 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 87 161
  (Polychromatic418967fa.accept_9_5_6_8_1_101 59 87 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 87 161 (accept_3_2 58 87 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  87 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 87 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 87 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 87 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 87 161 (accept_3_2 55 87 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 87 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 87 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 87 161
  (Polychromatic418967fa.accept_13_1_9_5_1_1598 53 87 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 87 161 (accept_3_2 52 87 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  87 161 (Polychromatic418967fa.accept_20_11_7_1_1_8874 51 87 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 87 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 87 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 161 (accept_3_2 49 87 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 87 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 87 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 87 161
  (Polychromatic418967fa.accept_9_2_6_8_1_321 47 87 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 87 161 (accept_3_2 46 87 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  87 161 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 87 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 87 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 87 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 87 161 (accept_3_2 43 87 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 87 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 87 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 87 161
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 87 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 87 161 (accept_3_2 40 87 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  87 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 87 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 87 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 87 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 87 161 (accept_3_2 37 87 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 87 161 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 87 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 87 161
  (Polychromatic418967fa.accept_20_15_7_1_1_5885 35 87 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 87 161 (accept_3_2 34 87 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  87 161 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 87 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 87 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 87 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 161 (accept_3_2 31 87 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 87 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 87 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 161
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 87 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 87 161 (accept_3_2 28 87 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  87 161 (Polychromatic418967fa.accept_13_1_9_5_1_1598 27 87 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 87 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 87 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 161 (accept_3_2 25 87 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 87 161 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 87 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 161
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 87 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 87 161 (accept_3_2 22 87 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  87 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 87 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 87 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 87 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 161 (accept_3_2 19 87 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 87 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 87 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 161
  (Polychromatic418967fa.accept_13_4_9_5_1_1641 17 87 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 87 161 (accept_3_2 16 87 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  87 161 (Polychromatic418967fa.accept_13_2_9_5_1_959 15 87 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 87 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 87 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 161 (accept_3_2 13 87 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 87 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 87 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 161
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 87 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 87 161 (accept_3_2 10 87 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  87 161 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 87 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 87 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 87 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 161 (accept_3_2 7 87 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 87 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 87 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 161
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 87 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 87 161 (accept_3_2 4 87 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87
  161 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 87 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 87 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 87 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 161 (accept_3_2 1 87 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 87 161))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76
  86 161 (Eq.refl Bool.true) (allA_succ_of_accept 75 86 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 86 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 86 161
  (Polychromatic418967fa.accept_9_2_5_8_1_11 74 86 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 86 161 (accept_3_2 73 86 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  86 161 (Polychromatic418967fa.accept_10_2_6_1_1_1296 72 86 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 86 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 86 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 86 161 (accept_3_2 70 86 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 86 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 86 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 86 161
  (Polychromatic418967fa.accept_11_2_9_7_1_124 68 86 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 86 161 (accept_3_2 67 86 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  86 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 86 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 86 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 86 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 86 161 (accept_3_2 64 86 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 86 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 86 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 86 161
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 62 86 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 86 161 (accept_3_2 61 86 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  86 161 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 86 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 86 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 86 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 86 161 (accept_3_2 58 86 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 86 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 86 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 86 161
  (Polychromatic418967fa.accept_9_2_5_8_1_11 56 86 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 86 161 (accept_3_2 55 86 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  86 161 (Polychromatic418967fa.accept_14_12_2_7_1_1243 54 86 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 86 161 (Polychromatic418967fa.accept_13_1_8_5_1_2315 53 86 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 86 161 (accept_3_2 52 86 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 86 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 86 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 86 161
  (Polychromatic418967fa.accept_16_2_6_1_1_2069 50 86 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 86 161 (accept_3_2 49 86 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  86 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 86 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 86 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 86 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 86 161 (accept_3_2 46 86 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 86 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 86 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 86 161
  (Polychromatic418967fa.accept_12_8_2_5_1_844 44 86 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 86 161 (accept_3_2 43 86 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  86 161 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 86 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 86 161 (Polychromatic418967fa.accept_17_7_1_8_1_6280 41 86 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 86 161 (accept_3_2 40 86 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 86 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 86 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 86 161
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 86 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 86 161 (accept_3_2 37 86 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  86 161 (Polychromatic418967fa.accept_13_10_8_5_1_1616 36 86 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 86 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 86 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 86 161 (accept_3_2 34 86 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 86 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 86 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 86 161
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 86 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 86 161 (accept_3_2 31 86 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  86 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 86 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 86 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 86 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 86 161 (accept_3_2 28 86 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 86 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 86 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 86 161
  (Polychromatic418967fa.accept_14_12_2_7_1_1243 26 86 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 86 161 (accept_3_2 25 86 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  86 161 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 86 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 86 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 86 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 86 161 (accept_3_2 22 86 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 86 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 86 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 86 161
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 86 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 86 161 (accept_3_2 19 86 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  86 161 (Polychromatic418967fa.accept_16_2_6_1_1_2069 18 86 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 86 161 (Polychromatic418967fa.accept_10_7_6_1_1_486 17 86 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 86 161 (accept_3_2 16 86 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 86 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 86 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 86 161
  (Polychromatic418967fa.accept_13_1_8_5_1_2315 14 86 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 86 161 (accept_3_2 13 86 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  86 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 86 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 86 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 86 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 86 161 (accept_3_2 10 86 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 86 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 86 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 161
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 86 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 86 161 (accept_3_2 7 86 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86
  161 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 86 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 86 161 (Polychromatic418967fa.accept_10_5_6_1_1_836 5 86 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 86 161 (accept_3_2 4 86 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 86 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 86 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 86 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 86
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 86 161 (accept_3_2 1 86 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  161)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 85 161 (Eq.refl
  Bool.true) (allA_of_3_0 77 85 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 78 84 161 (Eq.refl Bool.true)
  (allA_succ_of_gcd 77 84 161 7 11 12 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 76 84 161 (accept_3_2 76 84 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  84 161 (Polychromatic418967fa.accept_10_5_4_1_1_842 75 84 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 84 161 (Polychromatic418967fa.accept_9_2_3_8_1_318 74 84 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 84 161 (accept_3_2 73 84 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 84 161 (Polychromatic418967fa.accept_16_8_4_1_1_2102 72 84 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 84 161
  (Polychromatic418967fa.accept_19_14_8_9_1_4547 71 84 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 84 161 7 10 12 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 84 161 (Polychromatic418967fa.accept_8_5_4_1_1_111 69 84 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 84 161 (Polychromatic418967fa.accept_9_5_3_8_1_316 68 84 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 84 161 (accept_3_2 67 84 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 84 161 (Polychromatic418967fa.accept_13_1_6_5_1_1610
  66 84 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 84 161
  (Polychromatic418967fa.accept_9_2_3_8_1_318 65 84 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 84 161 (accept_3_2 64 84 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 84
  161 7 9 12 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62
  84 161 (Polychromatic418967fa.accept_13_10_6_5_1_2297 62 84 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 84 161 (accept_3_2 61 84 161 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 84 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 84 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 84 161 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 84 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 84 161 (accept_3_2 58 84 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 84 161 (Polychromatic418967fa.accept_10_7_4_1_1_1319
  57 84 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 84 161 7 8 12 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 84 161 (accept_3_2 55
  84 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 84 161
  (Polychromatic418967fa.accept_19_16_8_9_1_8858 54 84 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 84 161 (Polychromatic418967fa.accept_8_5_4_1_1_111 53 84 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 84 161 (accept_3_2 52 84 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 84 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 84 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 84 161 (Polychromatic418967fa.accept_9_5_3_8_1_316 50
  84 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 84 161 7 7 12 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 84 161
  (Polychromatic418967fa.accept_17_14_16_8_1_3861 48 84 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 84 161 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 84 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 84 161 (accept_3_2 46 84 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 84 161 (Polychromatic418967fa.accept_8_5_4_1_1_111 45 84 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 84 161 (Polychromatic418967fa.accept_16_12_4_1_1_1257
  44 84 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 84 161 (accept_3_2 43
  84 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 161 7 6 12 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 161
  (Polychromatic418967fa.accept_9_5_3_8_1_316 41 84 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 84 161 (accept_3_2 40 84 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  84 161 (Polychromatic418967fa.accept_19_1_8_9_1_3304 39 84 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 84 161 (Polychromatic418967fa.accept_9_2_3_8_1_318 38 84 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 84 161 (accept_3_2 37 84 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 84 161 (Polychromatic418967fa.accept_13_10_6_5_1_2297 36 84 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 84 161 7 5 12 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 84 161 (accept_3_2 34 84 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 84 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 84 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 84 161
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 84 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 84 161 (accept_3_2 31 84 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  84 161 (Polychromatic418967fa.accept_13_4_6_5_1_2333 30 84 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 84 161 (Polychromatic418967fa.accept_8_5_4_1_1_111 29 84 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 84 161 7 4 12 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 84 161 (Polychromatic418967fa.accept_10_7_4_1_1_1319
  27 84 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 84 161
  (Polychromatic418967fa.accept_17_9_16_8_1_2721 26 84 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 84 161 (accept_3_2 25 84 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  84 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 84 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 84 161 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 84 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 84 161 (accept_3_2 22 84 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 21 84 161 7 3 12 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 84 161 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 84 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 161 (accept_3_2 19 84 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 84 161 (Polychromatic418967fa.accept_19_18_8_9_1_3325 18 84
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 84 161
  (Polychromatic418967fa.accept_10_7_4_1_1_1319 17 84 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 84 161 (accept_3_2 16 84 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  84 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 84 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 84 161 7 2 12 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 84 161 (accept_3_2 13 84 161 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 84 161 (Polychromatic418967fa.accept_13_12_6_5_1_2335 12 84 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 84 161 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 84 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 84 161 (accept_3_2 10 84 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 84 161 (Polychromatic418967fa.accept_17_9_16_8_1_2721
  9 84 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 84 161
  (Polychromatic418967fa.accept_16_8_4_1_1_2102 8 84 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 84 161 7 1 12 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 84 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 84 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 84 161 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 84 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 84 161 (accept_3_2 4 84 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 84 161 (Polychromatic418967fa.accept_13_3_6_5_1_2336 3
  84 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 84 161
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 84 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 84 161 (accept_3_2 1 84 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  161)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 79 83 161 (Eq.refl
  Bool.true) (allA_succ_of_accept 78 83 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 83 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 161 (Polychromatic418967fa.accept_9_5_2_8_1_109 77
  83 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 83 161 (accept_3_2 76 83
  161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 83 161
  (Polychromatic418967fa.accept_9_3_2_8_1_108 75 83 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 83 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 83 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 161 (accept_3_2 73 83 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 83 161 (Polychromatic418967fa.accept_10_2_3_1_1_481 72 83 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 161 (Polychromatic418967fa.accept_14_1_13_7_1_1205
  71 83 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 83 161 (accept_3_2 70
  83 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 83 161
  (Polychromatic418967fa.accept_9_6_2_8_1_592 69 83 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 83 161 (Polychromatic418967fa.accept_9_5_2_8_1_109 68 83 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 161 (accept_3_2 67 83 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 83 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 83 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 161 (Polychromatic418967fa.accept_15_5_8_11_1_2350
  65 83 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 83 161 (accept_3_2 64
  83 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 83 161
  (Polychromatic418967fa.accept_15_3_8_11_1_4386 63 83 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 83 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 83 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 161 (accept_3_2 61 83 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 83 161 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 83 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 161 (Polychromatic418967fa.accept_9_5_2_8_1_109 59
  83 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 83 161 (accept_3_2 58 83
  161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 83 161
  (Polychromatic418967fa.accept_9_3_2_8_1_108 57 83 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 83 161 (Polychromatic418967fa.accept_11_1_6_7_1_116 56 83 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 161 (accept_3_2 55 83 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 83 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 83 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 161 (Polychromatic418967fa.accept_20_13_3_1_1_3065
  53 83 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 83 161 (accept_3_2 52
  83 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 83 161
  (Polychromatic418967fa.accept_9_6_2_8_1_592 51 83 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 83 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 83 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 161 (accept_3_2 49 83 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 83 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 83 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 161
  (Polychromatic418967fa.accept_17_13_15_8_1_3860 47 83 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 161 (accept_3_2 46 83 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 161 (Polychromatic418967fa.accept_11_1_6_7_1_116 45 83 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 161 (Polychromatic418967fa.accept_17_10_15_8_1_6324 44 83 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 161 (accept_3_2 43 83 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 83 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 161
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 83 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 161 (accept_3_2 40 83 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 83 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 83 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 161 (accept_3_2 37 83 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 161 (Polychromatic418967fa.accept_14_8_13_7_1_2798 36 83 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 161
  (Polychromatic418967fa.accept_15_5_8_11_1_2350 35 83 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 161 (accept_3_2 34 83 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 161 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 83 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 161 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 83 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 161 (accept_3_2 31 83 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 83 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 161
  (Polychromatic418967fa.accept_14_1_13_7_1_1205 29 83 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 161 (accept_3_2 28 83 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 161 (Polychromatic418967fa.accept_15_12_8_11_1_4383 27 83 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 83 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 161 (accept_3_2 25 83 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 161 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 83 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 161
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 83 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 161 (accept_3_2 22 83 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 83 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 161 (Polychromatic418967fa.accept_14_6_13_7_1_2015 20 83 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 161 (accept_3_2 19 83 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 83 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 161
  (Polychromatic418967fa.accept_19_17_7_9_1_3324 17 83 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 161 (accept_3_2 16 83 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 161 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 83 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 83 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 161 (accept_3_2 13 83 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 83 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 161
  (Polychromatic418967fa.accept_19_11_7_9_1_8873 11 83 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 161 (accept_3_2 10 83 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 161 (Polychromatic418967fa.accept_21_9_20_14_1_4139 9 83 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 161 (Polychromatic418967fa.accept_10_8_3_1_1_1316 8 83 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 161 (accept_3_2 7 83 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 83 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 161
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 83 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 161 (accept_3_2 4 83 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  161 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 83 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 83 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 83 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 161 (accept_3_2 1 83 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 161)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 80 82 161 (Eq.refl Bool.true) (allA_of_3_0 80 82 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ
  81 161 (allA_succ_of_accept 80 81 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 81 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 81 161 (accept_3_2 79 81 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 81 161 (Polychromatic418967fa.accept_15_3_6_11_1_855 78 81 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 161
  (Polychromatic418967fa.accept_15_2_6_11_1_1587 77 81 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 81 161 (accept_3_2 76 81 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  81 161 (Polychromatic418967fa.accept_12_3_9_5_1_853 75 81 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 81 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 81 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 81 161 (accept_3_2 73 81 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 81 161 (Polychromatic418967fa.accept_17_4_13_8_1_3874 72 81 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 161
  (Polychromatic418967fa.accept_13_6_3_5_1_3167 71 81 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 81 161 (accept_3_2 70 81 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  81 161 (Polychromatic418967fa.accept_11_3_4_7_1_114 69 81 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 81 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 81 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 81 161 (accept_3_2 67 81 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 81 161 (Polychromatic418967fa.accept_13_1_3_5_1_140 66 81 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 161
  (Polychromatic418967fa.accept_15_5_6_11_1_854 65 81 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 81 161 (accept_3_2 64 81 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  81 161 (Polychromatic418967fa.accept_11_8_4_7_1_1303 63 81 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 81 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 81 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 161 (accept_3_2 61 81 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 81 161 (Polychromatic418967fa.accept_13_8_3_5_1_1636 60 81 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 161
  (Polychromatic418967fa.accept_14_3_11_7_1_1260 59 81 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 81 161 (accept_3_2 58 81 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  81 161 (Polychromatic418967fa.accept_21_15_18_14_1_5632 57 81 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 81 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 81 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 161 (accept_3_2 55 81 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 81 161 (Polychromatic418967fa.accept_13_2_3_5_1_2294 54 81 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 161
  (Polychromatic418967fa.accept_13_1_3_5_1_140 53 81 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 81 161 (accept_3_2 52 81 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  81 161 (Polychromatic418967fa.accept_12_3_9_5_1_853 51 81 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 81 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 81 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 81 161 (accept_3_2 49 81 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 81 161 (Polychromatic418967fa.accept_13_9_3_5_1_1605 48 81 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 161
  (Polychromatic418967fa.accept_11_3_4_7_1_114 47 81 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 81 161 (accept_3_2 46 81 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  81 161 (Polychromatic418967fa.accept_13_6_3_5_1_3167 45 81 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 81 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 81 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 161 (accept_3_2 43 81 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 81 161 (Polychromatic418967fa.accept_19_4_5_9_1_8855 42 81 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 161
  (Polychromatic418967fa.accept_11_8_4_7_1_1303 41 81 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 81 161 (accept_3_2 40 81 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  81 161 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 81 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 81 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 81 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 161 (accept_3_2 37 81 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 81 161 (Polychromatic418967fa.accept_11_3_4_7_1_114 36 81 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 161
  (Polychromatic418967fa.accept_13_9_3_5_1_1605 35 81 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 81 161 (accept_3_2 34 81 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  81 161 (Polychromatic418967fa.accept_15_3_6_11_1_855 33 81 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 81 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 81 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 161 (accept_3_2 31 81 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 81 161 (Polychromatic418967fa.accept_11_8_4_7_1_1303 30 81 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 161
  (Polychromatic418967fa.accept_24_5_9_17_1_8872 29 81 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 81 161 (accept_3_2 28 81 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  81 161 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 81 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 81 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 81 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 161 (accept_3_2 25 81 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 81 161 (Polychromatic418967fa.accept_13_11_3_5_1_982 24 81 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 161
  (Polychromatic418967fa.accept_19_4_5_9_1_8855 23 81 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 161 (accept_3_2 22 81 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  81 161 (Polychromatic418967fa.accept_13_8_3_5_1_1636 21 81 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 81 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 81 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 161 (accept_3_2 19 81 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 81 161 (Polychromatic418967fa.accept_14_4_11_7_1_1234 18 81 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 161
  (Polychromatic418967fa.accept_14_3_11_7_1_1260 17 81 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 81 161 (accept_3_2 16 81 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  81 161 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 81 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 81 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 81 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 161 (accept_3_2 13 81 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 81 161 (Polychromatic418967fa.accept_18_12_9_17_1_7428 12 81 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 161
  (Polychromatic418967fa.accept_13_11_3_5_1_982 11 81 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 81 161 (accept_3_2 10 81 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  81 161 (Polychromatic418967fa.accept_13_9_3_5_1_1605 9 81 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 81 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 81 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 161 (accept_3_2 7 81 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 161 (Polychromatic418967fa.accept_13_6_3_5_1_3167 6 81 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 161
  (Polychromatic418967fa.accept_15_5_6_11_1_854 5 81 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 161 (accept_3_2 4 81 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81
  161 (Polychromatic418967fa.accept_11_3_4_7_1_114 3 81 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 81 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 81 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 161 (accept_3_2 1 81 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 81 161)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 80 161 (allA_succ_of_accept 79 80 161 (accept_3_2 79 80 161 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 80 161 (Polychromatic418967fa.accept_17_10_12_8_1_2748 78 80 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 80 161 (Polychromatic418967fa.accept_13_12_2_5_1_1634 77 80
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 80 161 (accept_3_2 76 80 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 80 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 75
  80 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 80 161
  (Polychromatic418967fa.accept_12_2_8_5_1_408 74 80 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 80 161 (accept_3_2 73 80 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  80 161 (Polychromatic418967fa.accept_13_7_2_5_1_2344 72 80 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 80 161 (Polychromatic418967fa.accept_17_3_12_8_1_1688 71 80 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 80 161 (accept_3_2 70 80 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 80 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 80 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 80 161
  (Polychromatic418967fa.accept_13_3_2_5_1_1632 68 80 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 80 161 (accept_3_2 67 80 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  80 161 (Polychromatic418967fa.accept_15_6_5_11_1_2378 66 80 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 80 161 (Polychromatic418967fa.accept_11_10_3_7_1_2564 65 80 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 80 161 (accept_3_2 64 80 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 80 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 80 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 80 161
  (Polychromatic418967fa.accept_12_2_8_5_1_408 62 80 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 80 161 (accept_3_2 61 80 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  80 161 (Polychromatic418967fa.accept_14_4_10_7_1_1946 60 80 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 80 161 (Polychromatic418967fa.accept_11_4_3_7_1_828 59 80 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 80 161 (accept_3_2 58 80 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 80 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 80 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 80 161
  (Polychromatic418967fa.accept_13_4_2_5_1_4045 56 80 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 80 161 (accept_3_2 55 80 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  80 161 (Polychromatic418967fa.accept_11_10_3_7_1_2564 54 80 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 80 161 (Polychromatic418967fa.accept_14_11_10_7_1_1948 53 80 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 80 161 (accept_3_2 52 80 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 80 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 80 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 80 161
  (Polychromatic418967fa.accept_12_2_8_5_1_408 50 80 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 80 161 (accept_3_2 49 80 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  80 161 (Polychromatic418967fa.accept_11_4_3_7_1_828 48 80 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 80 161 (Polychromatic418967fa.accept_15_2_5_11_1_1563 47 80 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 80 161 (accept_3_2 46 80 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 80 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 80 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 80 161
  (Polychromatic418967fa.accept_17_10_12_8_1_2748 44 80 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 80 161 (accept_3_2 43 80 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  80 161 (Polychromatic418967fa.accept_13_3_2_5_1_1632 42 80 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 80 161 (Polychromatic418967fa.accept_18_5_8_17_1_3478 41 80 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 80 161 (accept_3_2 40 80 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 80 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 80 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 80 161
  (Polychromatic418967fa.accept_12_2_8_5_1_408 38 80 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 80 161 (accept_3_2 37 80 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  80 161 (Polychromatic418967fa.accept_13_10_2_5_1_1633 36 80 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 80 161 (Polychromatic418967fa.accept_13_9_2_5_1_2310 35 80 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 80 161 (accept_3_2 34 80 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 80 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 80 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 80 161
  (Polychromatic418967fa.accept_11_10_3_7_1_2564 32 80 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 80 161 (accept_3_2 31 80 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  80 161 (Polychromatic418967fa.accept_13_4_2_5_1_4045 30 80 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 80 161 (Polychromatic418967fa.accept_13_3_2_5_1_1632 29 80 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 80 161 (accept_3_2 28 80 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 80 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 80 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 80 161
  (Polychromatic418967fa.accept_11_4_3_7_1_828 26 80 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 80 161 (accept_3_2 25 80 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  80 161 (Polychromatic418967fa.accept_15_9_5_11_1_5416 24 80 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 80 161 (Polychromatic418967fa.accept_13_10_2_5_1_1633 23 80 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 80 161 (accept_3_2 22 80 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 80 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 80 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 80 161
  (Polychromatic418967fa.accept_13_7_2_5_1_2344 20 80 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 80 161 (accept_3_2 19 80 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  80 161 (Polychromatic418967fa.accept_14_4_10_7_1_1946 18 80 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 80 161 (Polychromatic418967fa.accept_13_4_2_5_1_4045 17 80 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 80 161 (accept_3_2 16 80 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 80 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 80 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 80 161
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 80 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 80 161 (accept_3_2 13 80 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  80 161 (Polychromatic418967fa.accept_13_12_2_5_1_1634 12 80 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 80 161 (Polychromatic418967fa.accept_14_11_10_7_1_1948 11 80 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 80 161 (accept_3_2 10 80 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 80 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 80 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 80 161
  (Polychromatic418967fa.accept_15_8_5_11_1_2358 8 80 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 80 161 (accept_3_2 7 80 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 80
  161 (Polychromatic418967fa.accept_15_6_5_11_1_2378 6 80 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 80 161 (Polychromatic418967fa.accept_17_5_12_8_1_6304 5 80 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 80 161 (accept_3_2 4 80 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 80 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 80 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 80 161
  (Polychromatic418967fa.accept_12_2_8_5_1_408 2 80 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 80 161 (accept_3_2 1 80 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  161)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 79 161 (allA_of_3_0 79
  79 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 78 161 (allA_succ_of_accept 77 78 161
  (Polychromatic418967fa.accept_9_5_6_8_1_101 77 78 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 78 161 (accept_3_2 76 78 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  78 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 78 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 78 161 (Polychromatic418967fa.accept_9_2_6_8_1_321 74 78 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 78 161 (accept_3_2 73 78 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 78 161 (Polychromatic418967fa.accept_11_6_1_7_1_1315 72 78 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 78 161
  (Polychromatic418967fa.accept_4_3_2_1_1_50 71 78 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 78 161 (accept_3_2 70 78 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  78 161 (Polychromatic418967fa.accept_10_9_8_1_1_1331 69 78 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 78 161 (Polychromatic418967fa.accept_9_5_6_8_1_101 68 78 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 161 (accept_3_2 67 78 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 78 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 78 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 78 161
  (Polychromatic418967fa.accept_9_2_6_8_1_321 65 78 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 78 161 (accept_3_2 64 78 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  78 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 78 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 78 161 (Polychromatic418967fa.accept_14_6_8_7_1_589 62 78 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 161 (accept_3_2 61 78 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 78 161 (Polychromatic418967fa.accept_21_18_15_14_1_8871 60 78 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 78 161
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 78 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 78 161 (accept_3_2 58 78 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  78 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 78 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 78 161 (Polychromatic418967fa.accept_9_2_6_8_1_321 56 78 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 78 161 (accept_3_2 55 78 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 78 161 (Polychromatic418967fa.accept_21_12_15_14_1_8851 54 78 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 78 161
  (Polychromatic418967fa.accept_10_3_8_1_1_182 53 78 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 78 161 (accept_3_2 52 78 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  78 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 78 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 78 161 (Polychromatic418967fa.accept_9_5_6_8_1_101 50 78 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 161 (accept_3_2 49 78 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 78 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 78 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 78 161
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 78 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 78 161 (accept_3_2 46 78 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  78 161 (Polychromatic418967fa.accept_16_13_14_1_1_2094 45 78 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 78 161 (Polychromatic418967fa.accept_15_14_3_11_1_850 44 78 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 161 (accept_3_2 43 78 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 78 161 (Polychromatic418967fa.accept_19_4_2_9_1_4584 42 78 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 78 161
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 78 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 78 161 (accept_3_2 40 78 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  78 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 78 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 78 161 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 78 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 78 161 (accept_3_2 37 78 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 78 161 (Polychromatic418967fa.accept_15_6_3_11_1_848 36 78 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 78 161
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 78 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 78 161 (accept_3_2 34 78 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  78 161 (Polychromatic418967fa.accept_10_3_8_1_1_182 33 78 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 78 161 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 78 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 161 (accept_3_2 31 78 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 78 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 78 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 78 161
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 78 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 78 161 (accept_3_2 28 78 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  78 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 78 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 78 161 (Polychromatic418967fa.accept_19_7_2_9_1_6006 26 78 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 161 (accept_3_2 25 78 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 78 161 (Polychromatic418967fa.accept_21_3_15_14_1_5722 24 78 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 78 161
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 78 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 78 161 (accept_3_2 22 78 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  78 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 78 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 78 161 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 78 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 161 (accept_3_2 19 78 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 161 (Polychromatic418967fa.accept_19_18_2_9_1_8870 18 78 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 78 161
  (Polychromatic418967fa.accept_11_6_1_7_1_1315 17 78 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 78 161 (accept_3_2 16 78 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  78 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 78 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 78 161 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 78 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 161 (accept_3_2 13 78 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 78 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 78 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 78 161
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 78 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 78 161 (accept_3_2 10 78 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  78 161 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 78 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 78 161 (Polychromatic418967fa.accept_15_8_3_11_1_849 8 78 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 161 (accept_3_2 7 78 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 78 161 (Polychromatic418967fa.accept_11_6_1_7_1_1315 6 78 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 78 161
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 78 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 78 161 (accept_3_2 4 78 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 78
  161 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 78 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 78 161 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 78 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 78 161 (accept_3_2 1 78 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 78 161)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  77 161 (allA_succ_of_accept 76 77 161 (accept_3_2 76 77 161 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 77 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 75 77 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 77 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 74 77 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 161 (accept_3_2 73 77 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 161 (Polychromatic418967fa.accept_13_7_12_5_1_1603
  72 77 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 161
  (Polychromatic418967fa.accept_13_6_12_5_1_2304 71 77 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 77 161 7 10 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 77 161 (Polychromatic418967fa.accept_9_6_5_8_1_598 69 77 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 77 161 (Polychromatic418967fa.accept_8_4_5_1_1_299 68 77 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 161 (accept_3_2 67 77 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 66
  77 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 161
  (Polychromatic418967fa.accept_9_2_5_8_1_11 65 77 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 161 (accept_3_2 64 77 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 77
  161 7 9 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62
  77 161 (Polychromatic418967fa.accept_16_14_13_1_1_5278 62 77 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 77 161 (accept_3_2 61 77 161 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 77 161 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 77 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 161 (Polychromatic418967fa.accept_13_7_12_5_1_1603 59 77
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 77 161 (accept_3_2 58 77 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 77 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 57
  77 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 77 161 7 8 11 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 77 161 (accept_3_2 55
  77 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 161
  (Polychromatic418967fa.accept_10_4_7_1_1_471 54 77 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 77 161 (Polychromatic418967fa.accept_13_1_12_5_1_1601 53 77 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 77 161 (accept_3_2 52 77 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 77 161 (Polychromatic418967fa.accept_9_6_5_8_1_598 51 77 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 77 161 (Polychromatic418967fa.accept_15_5_2_11_1_1596
  50 77 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 77 161 7 7 11 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 77 161
  (Polychromatic418967fa.accept_9_3_5_8_1_99 48 77 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 77 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 77 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 77 161 (accept_3_2 46 77 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 77 161 (Polychromatic418967fa.accept_13_6_12_5_1_2304 45 77 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 77 161
  (Polychromatic418967fa.accept_8_4_5_1_1_299 44 77 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 77 161 (accept_3_2 43 77 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 77
  161 7 6 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  77 161 (Polychromatic418967fa.accept_13_2_12_5_1_1602 41 77 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 77 161 (accept_3_2 40 77 161 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 77 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 77 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 77 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 77 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 161 (accept_3_2 37 77 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 161 (Polychromatic418967fa.accept_8_4_5_1_1_299 36
  77 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 77 161 7 5 11 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 77 161 (accept_3_2 34
  77 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 77 161
  (Polychromatic418967fa.accept_9_6_5_8_1_598 33 77 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 77 161 (Polychromatic418967fa.accept_13_6_12_5_1_2304 32 77 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 161 (accept_3_2 31 77 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 77 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 77 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 29
  77 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 77 161 7 4 11 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 77 161
  (Polychromatic418967fa.accept_13_1_12_5_1_1601 27 77 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 77 161 (Polychromatic418967fa.accept_10_6_7_1_1_1297 26 77 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 161 (accept_3_2 25 77 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 77 161 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 77 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 161 (Polychromatic418967fa.accept_17_6_9_8_1_6316
  23 77 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 77 161 (accept_3_2 22
  77 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 77 161 7 3 11 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 77 161
  (Polychromatic418967fa.accept_8_4_5_1_1_299 20 77 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 77 161 (accept_3_2 19 77 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  77 161 (Polychromatic418967fa.accept_17_1_9_8_1_7492 18 77 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 77 161 (Polychromatic418967fa.accept_13_4_12_5_1_476 17 77 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 77 161 (accept_3_2 16 77 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 77 161 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 77 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 77 161 7 2 11 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 77 161 (accept_3_2 13 77 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 161 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 77 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 161
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 77 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 161 (accept_3_2 10 77 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 161 (Polychromatic418967fa.accept_15_9_2_11_1_2391 9 77 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 161 (Polychromatic418967fa.accept_13_8_12_5_1_1604 8 77 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 77 161 7 1 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 77 161 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 77
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 161
  (Polychromatic418967fa.accept_15_5_2_11_1_1596 5 77 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 161 (accept_3_2 4 77 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  161 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 77 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 77 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 161 (accept_3_2 1 77 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 161))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  76 161 (allA_of_3_0 76 76 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 75 161 (allA_succ_of_accept 74 75
  161 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 75 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 75 161 (accept_3_2 73 75 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  75 161 (Polychromatic418967fa.accept_14_2_5_7_1_3767 72 75 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 75 161 (Polychromatic418967fa.accept_11_5_9_7_1_411 71 75 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 75 161 (accept_3_2 70 75 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 75 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 75 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 75 161 (accept_3_2 67 75 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  75 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 75 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 75 161 (Polychromatic418967fa.accept_9_2_3_8_1_318 65 75 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 161 (accept_3_2 64 75 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 161 (Polychromatic418967fa.accept_16_15_11_1_1_7767 63 75 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 161
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 75 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 161 (accept_3_2 61 75 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  75 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 75 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 75 161 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 75 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 161 (accept_3_2 58 75 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 161 (Polychromatic418967fa.accept_11_2_9_7_1_124 57 75 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 75 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 75 161 (accept_3_2 55 75 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  75 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 75 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 75 161 (Polychromatic418967fa.accept_19_15_18_9_1_8869 53 75 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 161 (accept_3_2 52 75 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 75 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 161
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 75 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 75 161 (accept_3_2 49 75 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  75 161 (Polychromatic418967fa.accept_17_14_7_8_1_7544 48 75 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 75 161 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 75 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 161 (accept_3_2 46 75 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 161 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 75 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 75 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 75 161 (accept_3_2 43 75 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  75 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 75 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 75 161 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 75 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 161 (accept_3_2 40 75 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 161 (Polychromatic418967fa.accept_10_9_5_1_1_1325 39 75 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 161
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 75 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 75 161 (accept_3_2 37 75 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  75 161 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 75 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 75 161 (Polychromatic418967fa.accept_11_2_9_7_1_124 35 75 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 161 (accept_3_2 34 75 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 75 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 75 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 161 (accept_3_2 31 75 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  75 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 75 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 75 161 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 75 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 161 (accept_3_2 28 75 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 161 (Polychromatic418967fa.accept_11_5_9_7_1_411 27 75 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 161
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 75 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 75 161 (accept_3_2 25 75 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  75 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 75 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 75 161 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 75 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 161 (accept_3_2 22 75 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 161 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 75 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 75 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 75 161 (accept_3_2 19 75 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  75 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 75 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 75 161 (Polychromatic418967fa.accept_13_4_10_5_1_1644 17 75 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 161 (accept_3_2 16 75 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 75 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 161
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 75 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 161 (accept_3_2 13 75 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  75 161 (Polychromatic418967fa.accept_14_12_5_7_1_2010 12 75 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 75 161 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 75 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 161 (accept_3_2 10 75 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 161 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 75 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 75 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 161 (accept_3_2 7 75 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75
  161 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 75 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 161 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 75 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 161 (accept_3_2 4 75 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 75 161 (Polychromatic418967fa.accept_19_3_18_9_1_4580 3 75 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 75
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 161 (accept_3_2 1 75 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  161))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 161 (allA_succ_of_accept
  73 74 161 (accept_3_2 73 74 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 74 161
  (Polychromatic418967fa.accept_15_12_14_11_1_4375 72 74 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 74 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 74 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 74 161 (accept_3_2 70 74 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 74 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 74 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 74 161
  (Polychromatic418967fa.accept_9_5_2_8_1_109 68 74 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 74 161 (accept_3_2 67 74 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  74 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 74 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 74 161 (Polychromatic418967fa.accept_10_5_4_1_1_842 65 74 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 74 161 (accept_3_2 64 74 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 74 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 74 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 74 161
  (Polychromatic418967fa.accept_18_8_2_17_1_4782 62 74 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 74 161 (accept_3_2 61 74 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  74 161 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 74 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 74 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 74 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 74 161 (accept_3_2 58 74 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 74 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 74 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 74 161
  (Polychromatic418967fa.accept_12_8_2_5_1_844 56 74 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 74 161 (accept_3_2 55 74 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  74 161 (Polychromatic418967fa.accept_13_2_9_5_1_959 54 74 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 74 161 (Polychromatic418967fa.accept_13_1_9_5_1_1598 53 74 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 74 161 (accept_3_2 52 74 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 74 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 74 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 74 161
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 74 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 74 161 (accept_3_2 49 74 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  74 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 74 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 74 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 74 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 74 161 (accept_3_2 46 74 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 74 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 74 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 74 161
  (Polychromatic418967fa.accept_12_8_2_5_1_844 44 74 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 74 161 (accept_3_2 43 74 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  74 161 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 74 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 74 161 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 74 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 74 161 (accept_3_2 40 74 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 74 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 74 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 74 161
  (Polychromatic418967fa.accept_14_10_4_7_1_1214 38 74 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 74 161 (accept_3_2 37 74 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  74 161 (Polychromatic418967fa.accept_28_8_18_21_1_8868 36 74 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 74 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 74 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 74 161 (accept_3_2 34 74 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 74 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 74 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 74 161
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 74 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 74 161 (accept_3_2 31 74 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  74 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 74 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 74 161 (Polychromatic418967fa.accept_13_3_9_5_1_2340 29 74 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 74 161 (accept_3_2 28 74 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 74 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 74 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 74 161
  (Polychromatic418967fa.accept_11_4_8_7_1_819 26 74 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 74 161 (accept_3_2 25 74 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  74 161 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 74 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 74 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 74 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 74 161 (accept_3_2 22 74 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 74 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 74 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 74 161
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 74 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 74 161 (accept_3_2 19 74 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  74 161 (Polychromatic418967fa.accept_15_3_14_11_1_1579 18 74 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 74 161 (Polychromatic418967fa.accept_10_7_4_1_1_1319 17 74 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 74 161 (accept_3_2 16 74 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 74 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 74 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 74 161
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 74 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 74 161 (accept_3_2 13 74 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  74 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 74 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 74 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 74 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 74 161 (accept_3_2 10 74 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 74 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 74 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 74 161
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 74 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 74 161 (accept_3_2 7 74 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 74
  161 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 74 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 74 161 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 74 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 74 161 (accept_3_2 4 74 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 74 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 74 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 74 161 (Polychromatic418967fa.accept_13_2_9_5_1_959 2
  74 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 161 (accept_3_2 1 74 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  161)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73 161 (allA_of_3_0 73 73 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 72 161 (allA_succ_of_accept 71 72 161
  (Polychromatic418967fa.accept_16_7_8_1_1_3061 71 72 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 72 161 (accept_3_2 70 72 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  72 161 (Polychromatic418967fa.accept_10_9_2_1_1_840 69 72 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 72 161 (Polychromatic418967fa.accept_14_12_2_7_1_1243 68 72 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 72 161 (accept_3_2 67 72 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 72 161 (Polychromatic418967fa.accept_10_6_2_1_1_494 66 72 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 72 161
  (Polychromatic418967fa.accept_14_9_2_7_1_1242 65 72 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 72 161 (accept_3_2 64 72 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  72 161 (Polychromatic418967fa.accept_10_3_2_1_1_839 63 72 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 72 161 (Polychromatic418967fa.accept_19_5_15_9_1_4592 62 72 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 161 (accept_3_2 61 72 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 72 161 (Polychromatic418967fa.accept_16_12_8_1_1_5270 60 72
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 72 161
  (Polychromatic418967fa.accept_10_9_2_1_1_840 59 72 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 72 161 (accept_3_2 58 72 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  72 161 (Polychromatic418967fa.accept_16_9_8_1_1_1228 57 72 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 72 161 (Polychromatic418967fa.accept_10_6_2_1_1_494 56 72 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 161 (accept_3_2 55 72 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 72 161 (Polychromatic418967fa.accept_13_2_7_5_1_3189 54 72 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 72 161
  (Polychromatic418967fa.accept_10_3_2_1_1_839 53 72 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 72 161 (accept_3_2 52 72 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  72 161 (Polychromatic418967fa.accept_13_12_7_5_1_3147 51 72 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 72 161 (Polychromatic418967fa.accept_13_11_7_5_1_2314 50 72 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 72 161 (accept_3_2 49 72 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 72 161 (Polychromatic418967fa.accept_19_10_15_9_1_396 48 72
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 72 161
  (Polychromatic418967fa.accept_14_5_2_7_1_2804 47 72 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 72 161 (accept_3_2 46 72 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  72 161 (Polychromatic418967fa.accept_11_1_6_7_1_116 45 72 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 72 161 (Polychromatic418967fa.accept_15_14_12_11_1_1572 44 72 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 161 (accept_3_2 43 72 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 72 161 (Polychromatic418967fa.accept_19_4_15_9_1_8845 42 72
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 72 161
  (Polychromatic418967fa.accept_13_2_7_5_1_3189 41 72 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 72 161 (accept_3_2 40 72 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  72 161 (Polychromatic418967fa.accept_10_9_2_1_1_840 39 72 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 72 161 (Polychromatic418967fa.accept_13_12_7_5_1_3147 38 72 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 161 (accept_3_2 37 72 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 72 161 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 72 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 72 161
  (Polychromatic418967fa.accept_17_1_4_8_1_5049 35 72 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 72 161 (accept_3_2 34 72 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  72 161 (Polychromatic418967fa.accept_10_3_2_1_1_839 33 72 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 72 161 (Polychromatic418967fa.accept_19_13_15_9_1_3293 32 72 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 72 161 (accept_3_2 31 72 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 72 161 (Polychromatic418967fa.accept_17_13_4_8_1_3830 30 72
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 72 161
  (Polychromatic418967fa.accept_10_9_2_1_1_840 29 72 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 72 161 (accept_3_2 28 72 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  72 161 (Polychromatic418967fa.accept_21_6_9_14_1_8867 27 72 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 72 161 (Polychromatic418967fa.accept_10_6_2_1_1_494 26 72 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 161 (accept_3_2 25 72 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 72 161 (Polychromatic418967fa.accept_13_11_7_5_1_2314 24 72 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 72 161
  (Polychromatic418967fa.accept_10_3_2_1_1_839 23 72 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 72 161 (accept_3_2 22 72 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  72 161 (Polychromatic418967fa.accept_19_2_15_9_1_7318 21 72 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 72 161 (Polychromatic418967fa.accept_16_4_8_1_1_5257 20 72 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 161 (accept_3_2 19 72 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 72 161 (Polychromatic418967fa.accept_17_1_4_8_1_5049 18 72 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 72 161
  (Polychromatic418967fa.accept_21_17_9_14_1_5700 17 72 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 72 161 (accept_3_2 16 72 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  72 161 (Polychromatic418967fa.accept_13_2_7_5_1_3189 15 72 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 72 161 (Polychromatic418967fa.accept_15_14_12_11_1_1572 14 72 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 161 (accept_3_2 13 72 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 72 161 (Polychromatic418967fa.accept_11_1_6_7_1_116 12 72 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 72 161
  (Polychromatic418967fa.accept_13_11_7_5_1_2314 11 72 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 72 161 (accept_3_2 10 72 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  72 161 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 72 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 72 161 (Polychromatic418967fa.accept_15_8_12_11_1_1570 8 72 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 161 (accept_3_2 7 72 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 72 161 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 72 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 72 161
  (Polychromatic418967fa.accept_14_5_2_7_1_2804 5 72 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 72 161 (accept_3_2 4 72 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 72
  161 (Polychromatic418967fa.accept_10_3_2_1_1_839 3 72 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 72 161 (Polychromatic418967fa.accept_13_2_7_5_1_3189 2 72 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 161 (accept_3_2 1 72 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 72 161)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 161
  (allA_succ_of_accept 70 71 161 (accept_3_2 70 71 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  71 161 (Polychromatic418967fa.accept_13_4_6_5_1_2333 69 71 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 71 161 (Polychromatic418967fa.accept_13_3_6_5_1_2336 68 71 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 161 (accept_3_2 67 71 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 71 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 161
  (Polychromatic418967fa.accept_19_8_14_9_1_4590 65 71 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 161 (accept_3_2 64 71 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 161 (Polychromatic418967fa.accept_13_11_6_5_1_2339 63 71 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 71 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 161 (accept_3_2 61 71 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 161 (Polychromatic418967fa.accept_19_3_14_9_1_8866 60 71 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 161
  (Polychromatic418967fa.accept_21_17_8_14_1_5638 59 71 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 161 (accept_3_2 58 71 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 161 (Polychromatic418967fa.accept_20_17_11_1_1_8865 57 71 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 161 (Polychromatic418967fa.accept_13_4_6_5_1_2333 56 71 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 161 (accept_3_2 55 71 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 71 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 161
  (Polychromatic418967fa.accept_11_9_5_7_1_815 53 71 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 161 (accept_3_2 52 71 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 161 (Polychromatic418967fa.accept_13_12_6_5_1_2335 51 71 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 71 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 161 (accept_3_2 49 71 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 161 (Polychromatic418967fa.accept_14_6_1_7_1_2775 48 71 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 161
  (Polychromatic418967fa.accept_17_13_3_8_1_6310 47 71 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 161 (accept_3_2 46 71 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 161 (Polychromatic418967fa.accept_21_3_8_14_1_8864 45 71 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 161 (Polychromatic418967fa.accept_19_6_14_9_1_8863 44 71 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 161 (accept_3_2 43 71 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 71 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 161
  (Polychromatic418967fa.accept_14_13_1_7_1_1211 41 71 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 161 (accept_3_2 40 71 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 161 (Polychromatic418967fa.accept_17_5_3_8_1_1697 39 71 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 71 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 161 (accept_3_2 37 71 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 161 (Polychromatic418967fa.accept_13_10_6_5_1_2297 36 71 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 161
  (Polychromatic418967fa.accept_19_16_14_9_1_7316 35 71 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 161 (accept_3_2 34 71 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 161 (Polychromatic418967fa.accept_21_12_8_14_1_8862 33 71 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 161 (Polychromatic418967fa.accept_20_12_11_1_1_3032 32 71 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 161 (accept_3_2 31 71 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 71 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 161
  (Polychromatic418967fa.accept_13_3_6_5_1_2336 29 71 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 161 (accept_3_2 28 71 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 161 (Polychromatic418967fa.accept_13_1_6_5_1_1610 27 71 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 71 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 161 (accept_3_2 25 71 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 161 (Polychromatic418967fa.accept_13_11_6_5_1_2339 24 71 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 161
  (Polychromatic418967fa.accept_13_10_6_5_1_2297 23 71 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 161 (accept_3_2 22 71 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 161 (Polychromatic418967fa.accept_26_21_19_5_1_8861 21 71 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 161 (Polychromatic418967fa.accept_11_9_5_7_1_815 20 71 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 161 (accept_3_2 19 71 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 71 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 161
  (Polychromatic418967fa.accept_13_4_6_5_1_2333 17 71 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 161 (accept_3_2 16 71 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 161 (Polychromatic418967fa.accept_21_15_8_14_1_8860 15 71 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 71 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 161 (accept_3_2 13 71 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 161 (Polychromatic418967fa.accept_13_12_6_5_1_2335 12 71 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 161
  (Polychromatic418967fa.accept_13_11_6_5_1_2339 11 71 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 161 (accept_3_2 10 71 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 161 (Polychromatic418967fa.accept_11_9_5_7_1_815 9 71 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 161 (Polychromatic418967fa.accept_14_8_1_7_1_3725 8 71 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 161 (accept_3_2 7 71 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 71 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 161
  (Polychromatic418967fa.accept_17_5_3_8_1_1697 5 71 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 161 (accept_3_2 4 71 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  161 (Polychromatic418967fa.accept_13_3_6_5_1_2336 3 71 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 71 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 71 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 161 (accept_3_2 1 71 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 71 161)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 70 161 (allA_of_3_0 70 70 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 69 161
  (allA_succ_of_accept 68 69 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 69 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 69 161 (accept_3_2 67 69 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 69 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 69 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 69 161 (Polychromatic418967fa.accept_9_2_6_8_1_321 65
  69 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 161 (accept_3_2 64 69
  161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 161
  (Polychromatic418967fa.accept_12_3_9_5_1_853 63 69 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 69 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 69 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 161 (accept_3_2 61 69 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 69 161 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 69 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 69 161 (Polychromatic418967fa.accept_9_5_6_8_1_101 59
  69 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 161 (accept_3_2 58 69
  161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 161
  (Polychromatic418967fa.accept_9_3_6_8_1_308 57 69 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 69 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 69 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 69 161 (accept_3_2 55 69 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 69 161 (Polychromatic418967fa.accept_11_10_3_7_1_2564 54 69 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 69 161
  (Polychromatic418967fa.accept_13_1_4_5_1_113 53 69 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 69 161 (accept_3_2 52 69 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  69 161 (Polychromatic418967fa.accept_12_3_9_5_1_853 51 69 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 69 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 69 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 161 (accept_3_2 49 69 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 69 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 69 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 69 161
  (Polychromatic418967fa.accept_9_2_6_8_1_321 47 69 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 69 161 23 2 3 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 69 161 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 69 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 69 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 161 (accept_3_2 43 69 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 69 161 (Polychromatic418967fa.accept_10_2_9_1_1_185
  42 69 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 69 161
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 69 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 69 161 (accept_3_2 40 69 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  69 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 69 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 69 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 69 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 69 161 (accept_3_2 37 69 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 69 161 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 69 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 69 161
  (Polychromatic418967fa.accept_10_5_9_1_1_187 35 69 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 69 161 (accept_3_2 34 69 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  69 161 (Polychromatic418967fa.accept_19_14_12_9_1_4587 33 69 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 69 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 69 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 161 (accept_3_2 31 69 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 69 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 69 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 161
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 69 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 69 161 (accept_3_2 28 69 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  69 161 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 69 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 69 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 69 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 161 (accept_3_2 25 69 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 69 161 (Polychromatic418967fa.accept_17_7_1_8_1_6280 24 69 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 23 69 161 23 1 3 7 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 22 69 161 (accept_3_2 22 69 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 69 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 69 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 161 (accept_3_2 19 69 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  69 161 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 69 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 69 161 (Polychromatic418967fa.accept_15_2_9_11_1_1551 17 69 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 161 (accept_3_2 16 69 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 161 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 69 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 69 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 161 (accept_3_2 13 69 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  69 161 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 69 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 69 161 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 69 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 161 (accept_3_2 10 69 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 161 (Polychromatic418967fa.accept_13_9_4_5_1_1651 9 69 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 69 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 161 (accept_3_2 7 69 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69
  161 (Polychromatic418967fa.accept_13_6_4_5_1_2330 6 69 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 69 161 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 69 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 161 (accept_3_2 4 69 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 69 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 69 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 69 161 (accept_3_2 1 69 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  161))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 161 (allA_succ_of_accept 67 68
  161 (accept_3_2 67 68 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 68 161
  (Polychromatic418967fa.accept_9_3_5_8_1_99 66 68 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 68 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 68 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 68 161 (accept_3_2 64 68 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 68 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 68 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 68 161 (Polychromatic418967fa.accept_12_2_8_5_1_408
  62 68 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 68 161 (accept_3_2 61
  68 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 68 161
  (Polychromatic418967fa.accept_9_6_5_8_1_598 60 68 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 68 161 (Polychromatic418967fa.accept_10_9_8_1_1_1331 59 68 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 68 161 (accept_3_2 58 68 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 68 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 68 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 68 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 56
  68 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 68 161 (accept_3_2 55 68
  161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 68 161
  (Polychromatic418967fa.accept_13_2_3_5_1_2294 54 68 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 68 161 (Polychromatic418967fa.accept_8_5_4_1_1_111 53 68 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 68 161 (accept_3_2 52 68 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 68 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 68 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 68 161 (Polychromatic418967fa.accept_12_2_8_5_1_408
  50 68 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 68 161 (accept_3_2 49
  68 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 68 161
  (Polychromatic418967fa.accept_9_3_5_8_1_99 48 68 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 68 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 68 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 68 161 (accept_3_2 46 68 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 68 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 68 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 68 161 (Polychromatic418967fa.accept_14_2_12_7_1_617
  44 68 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 68 161 (accept_3_2 43
  68 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 68 161
  (Polychromatic418967fa.accept_9_6_5_8_1_598 42 68 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 68 161 (Polychromatic418967fa.accept_13_2_3_5_1_2294 41 68 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 68 161 (accept_3_2 40 68 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 68 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 68 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 68 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 38
  68 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 68 161 (accept_3_2 37 68
  161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 68 161
  (Polychromatic418967fa.accept_19_17_11_9_1_2141 36 68 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 68 161 (Polychromatic418967fa.accept_13_9_3_5_1_1605 35 68 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 68 161 (accept_3_2 34 68 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 68 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 68 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 161 (Polychromatic418967fa.accept_13_6_3_5_1_3167
  32 68 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 68 161 (accept_3_2 31
  68 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 68 161
  (Polychromatic418967fa.accept_9_3_5_8_1_99 30 68 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 68 161 (Polychromatic418967fa.accept_8_5_4_1_1_111 29 68 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 68 161 (accept_3_2 28 68 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 68 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 68 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 68 161 (Polychromatic418967fa.accept_12_2_8_5_1_408
  26 68 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 68 161 (accept_3_2 25
  68 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 68 161
  (Polychromatic418967fa.accept_9_6_5_8_1_598 24 68 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 68 161 (Polychromatic418967fa.accept_10_3_8_1_1_182 23 68 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 68 161 (accept_3_2 22 68 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 68 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 68 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 68 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 20
  68 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 68 161 (accept_3_2 19 68
  161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 68 161
  (Polychromatic418967fa.accept_15_3_8_11_1_4386 18 68 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 68 161 (Polychromatic418967fa.accept_19_17_11_9_1_2141 17 68 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 68 161 (accept_3_2 16 68 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 68 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 68 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 68 161 (Polychromatic418967fa.accept_12_2_8_5_1_408
  14 68 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 68 161 (accept_3_2 13
  68 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 68 161
  (Polychromatic418967fa.accept_9_3_5_8_1_99 12 68 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 68 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 68 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 68 161 (accept_3_2 10 68 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 68 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 68 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 68 161 (Polychromatic418967fa.accept_13_8_3_5_1_1636 8
  68 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 68 161 (accept_3_2 7 68 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 68 161 (Polychromatic418967fa.accept_9_6_5_8_1_598 6
  68 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 68 161
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 68 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 68 161 (accept_3_2 4 68 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 68
  161 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 68 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 68 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 68 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 161 (accept_3_2 1 68 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 68 161)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 161
  (allA_of_3_0 67 67 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 66 161 (allA_succ_of_accept 65 66 161
  (Polychromatic418967fa.accept_9_2_3_8_1_318 65 66 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 66 161 (accept_3_2 64 66 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  66 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 66 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 66 161 (Polychromatic418967fa.accept_10_2_6_1_1_1296 62 66 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 66 161 (accept_3_2 61 66 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 66 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 66 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 66 161
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 66 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 66 161 (accept_3_2 58 66 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  66 161 (Polychromatic418967fa.accept_10_7_6_1_1_486 57 66 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 66 161 (Polychromatic418967fa.accept_9_2_3_8_1_318 56 66 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 66 161 (accept_3_2 55 66 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 66 161 (Polychromatic418967fa.accept_15_9_6_11_1_1586 54 66 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 66 161
  (Polychromatic418967fa.accept_14_11_10_7_1_1948 53 66 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 66 161 (accept_3_2 52 66 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  66 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 66 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 66 161 (Polychromatic418967fa.accept_9_5_3_8_1_316 50 66 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 161 (accept_3_2 49 66 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 66 161 (Polychromatic418967fa.accept_13_9_1_5_1_964 48 66 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 66 161
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 66 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 66 161 (accept_3_2 46 66 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  66 161 (Polychromatic418967fa.accept_10_5_6_1_1_836 45 66 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 66 161 (Polychromatic418967fa.accept_16_12_2_1_1_1215 44 66 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 66 161 (accept_3_2 43 66 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 66 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 66 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 66 161
  (Polychromatic418967fa.accept_9_5_3_8_1_316 41 66 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 66 161 (accept_3_2 40 66 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  66 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 66 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 66 161 (Polychromatic418967fa.accept_9_2_3_8_1_318 38 66 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 66 161 (accept_3_2 37 66 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 66 161 (Polychromatic418967fa.accept_20_16_6_1_1_7270 36 66 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 66 161
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 66 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 66 161 (accept_3_2 34 66 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  66 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 66 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 66 161 (Polychromatic418967fa.accept_9_5_3_8_1_316 32 66 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 161 (accept_3_2 31 66 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 66 161 (Polychromatic418967fa.accept_13_4_1_5_1_1628 30 66 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 66 161
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 66 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 66 161 (accept_3_2 28 66 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  66 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 66 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 66 161 (Polychromatic418967fa.accept_25_1_16_11_1_8859 26 66 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 161 (accept_3_2 25 66 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 66 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 66 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 66 161
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 66 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 66 161 (accept_3_2 22 66 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  66 161 (Polychromatic418967fa.accept_13_8_1_5_1_3176 21 66 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 66 161 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 66 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 161 (accept_3_2 19 66 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 66 161 (Polychromatic418967fa.accept_14_4_10_7_1_1946 18 66 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 66 161
  (Polychromatic418967fa.accept_10_7_6_1_1_486 17 66 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 66 161 (accept_3_2 16 66 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  66 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 66 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 66 161 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 66 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 161 (accept_3_2 13 66 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 66 161 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 66 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 66 161
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 66 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 66 161 (accept_3_2 10 66 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  66 161 (Polychromatic418967fa.accept_13_9_1_5_1_964 9 66 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 66 161 (Polychromatic418967fa.accept_13_8_1_5_1_3176 8 66 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 161 (accept_3_2 7 66 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 66 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 66 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 66 161
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 66 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 66 161 (accept_3_2 4 66 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 66
  161 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 66 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 66 161 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 66 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 161 (accept_3_2 1 66 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 66 161)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 161
  (allA_succ_of_accept 64 65 161 (accept_3_2 64 65 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  65 161 (Polychromatic418967fa.accept_20_3_5_1_1_4391 63 65 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 65 161 (Polychromatic418967fa.accept_15_2_5_11_1_1563 62 65 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 161 (accept_3_2 61 65 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 65 161 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 65 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 161
  (Polychromatic418967fa.accept_9_5_2_8_1_109 59 65 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 65 161 (accept_3_2 58 65 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  65 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 57 65 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 65 161 (Polychromatic418967fa.accept_10_6_5_1_1_482 56 65 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 161 (accept_3_2 55 65 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 65 161 (Polychromatic418967fa.accept_10_4_5_1_1_497 54 65 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 161
  (Polychromatic418967fa.accept_15_8_5_11_1_2358 53 65 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 65 161 (accept_3_2 52 65 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  65 161 (Polychromatic418967fa.accept_9_6_2_8_1_592 51 65 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 65 161 (Polychromatic418967fa.accept_9_5_2_8_1_109 50 65 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 161 (accept_3_2 49 65 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 65 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 161
  (Polychromatic418967fa.accept_11_3_10_7_1_129 47 65 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 65 161 (accept_3_2 46 65 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  65 161 (Polychromatic418967fa.accept_17_11_14_8_1_2729 45 65 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 65 161 (Polychromatic418967fa.accept_10_4_5_1_1_497 44 65 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 161 (accept_3_2 43 65 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 161 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 65 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 161
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 65 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 65 161 (accept_3_2 40 65 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  65 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 65 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 65 161 (Polychromatic418967fa.accept_15_8_5_11_1_2358 38 65 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 161 (accept_3_2 37 65 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 161 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 65 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 161
  (Polychromatic418967fa.accept_19_16_8_9_1_8858 35 65 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 65 161 (accept_3_2 34 65 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  65 161 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 65 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 161 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 65 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 161 (accept_3_2 31 65 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 65 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 65 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 161
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 65 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 161 (accept_3_2 28 65 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  65 161 (Polychromatic418967fa.accept_21_6_2_14_1_5688 27 65 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 65 161 (Polychromatic418967fa.accept_10_6_5_1_1_482 26 65 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 161 (accept_3_2 25 65 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 161 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 65 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 161
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 65 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 161 (accept_3_2 22 65 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 65 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 161 (Polychromatic418967fa.accept_18_2_11_17_1_4773 20 65 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 161 (accept_3_2 19 65 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 161 (Polychromatic418967fa.accept_19_18_8_9_1_3325 18 65
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 161
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 17 65 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 161 (accept_3_2 16 65 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 161 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 65 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 161 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 65 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 161 (accept_3_2 13 65 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 65 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 161
  (Polychromatic418967fa.accept_17_11_14_8_1_2729 11 65 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 161 (accept_3_2 10 65 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 161 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 65 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 161 (Polychromatic418967fa.accept_15_8_5_11_1_2358 8 65 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 161 (accept_3_2 7 65 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 161 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 65 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 161
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 65 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 161 (accept_3_2 4 65 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  161 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 65 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 161 (Polychromatic418967fa.accept_14_2_9_7_1_5633 2 65 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 161 (accept_3_2 1 65 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 161))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 161
  (allA_of_3_0 64 64 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 63 161 (allA_succ_of_accept 62 63 161
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 63 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 161 (accept_3_2 61 63 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  63 161 (Polychromatic418967fa.accept_19_3_6_9_1_7334 60 63 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 63 161 (Polychromatic418967fa.accept_11_4_8_7_1_819 59 63 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 161 (accept_3_2 58 63 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 161 (Polychromatic418967fa.accept_12_9_3_5_1_423 57 63 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 63 161 7 8 9 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 63 161 (accept_3_2 55 63 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 63 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 63 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 63 161
  (Polychromatic418967fa.accept_15_8_3_11_1_849 53 63 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 63 161 (accept_3_2 52 63 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  63 161 (Polychromatic418967fa.accept_15_6_3_11_1_848 51 63 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 63 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 63 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 63 161 7 7 9 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 63 161 (Polychromatic418967fa.accept_10_8_3_1_1_1316
  48 63 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 63 161
  (Polychromatic418967fa.accept_22_3_19_7_1_8857 47 63 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 63 161 (accept_3_2 46 63 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  63 161 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 63 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 63 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 63 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 63 161 (accept_3_2 43 63 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 63 161 7 6 9 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 63 161 (Polychromatic418967fa.accept_19_3_6_9_1_7334 41 63 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 161 (accept_3_2 40 63 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 161 (Polychromatic418967fa.accept_17_5_12_8_1_6304 39 63
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 161
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 63 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 161 (accept_3_2 37 63 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  63 161 (Polychromatic418967fa.accept_15_6_3_11_1_848 36 63 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 63 161 7 5 9 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 34 63 161 (accept_3_2 34 63 161 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 63 161 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 63 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 63 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 161 (accept_3_2 31 63 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 63 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 30
  63 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 161
  (Polychromatic418967fa.accept_13_3_11_5_1_2348 29 63 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 63 161 7 4 9 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 63 161 (Polychromatic418967fa.accept_16_11_15_1_1_2074 27 63 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 63 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 161 (accept_3_2 25 63 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 63 161 (Polychromatic418967fa.accept_16_8_15_1_1_3006
  24 63 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 161
  (Polychromatic418967fa.accept_15_8_3_11_1_849 23 63 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 63 161 (accept_3_2 22 63 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 63
  161 7 3 9 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20
  63 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 63 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 63 161 (accept_3_2 19 63 161 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 63 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 63 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 161 (Polychromatic418967fa.accept_19_17_6_9_1_8856 17 63
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 161 (accept_3_2 16 63 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 161 (Polychromatic418967fa.accept_11_4_8_7_1_819
  15 63 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 63 161 7 2 9 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 63 161 (accept_3_2 13
  63 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 63 161
  (Polychromatic418967fa.accept_10_2_3_1_1_481 12 63 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 63 161 (Polychromatic418967fa.accept_16_11_15_1_1_2074 11 63 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 161 (accept_3_2 10 63 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 63 161 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 63 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 63
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 63 161 7 1 9 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 63 161
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 63 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 161 (Polychromatic418967fa.accept_16_5_15_1_1_2113 5 63 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 161 (accept_3_2 4 63 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 63 161 (Polychromatic418967fa.accept_13_3_11_5_1_2348 3 63 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 63
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 161 (accept_3_2 1 63 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  161))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 161 (allA_succ_of_accept 61 62 161
  (accept_3_2 61 62 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 62 161
  (Polychromatic418967fa.accept_13_8_10_5_1_977 60 62 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 62 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 62 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 62 161 (accept_3_2 58 62 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 62 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 62 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 62 161 (Polychromatic418967fa.accept_10_6_2_1_1_494
  56 62 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 62 161 (accept_3_2 55
  62 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 62 161
  (Polychromatic418967fa.accept_13_2_10_5_1_1643 54 62 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 62 161 (Polychromatic418967fa.accept_10_3_2_1_1_839 53 62 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 62 161 (accept_3_2 52 62 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 62 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 62 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 62 161 (Polychromatic418967fa.accept_14_8_6_7_1_1934
  50 62 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 62 161 (accept_3_2 49
  62 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 62 161
  (Polychromatic418967fa.accept_17_14_11_8_1_3854 48 62 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 62 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 62 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 62 161 (accept_3_2 46 62 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 62 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 62 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 62 161 (Polychromatic418967fa.accept_12_8_2_5_1_844
  44 62 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 62 161 (accept_3_2 43
  62 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 62 161
  (Polychromatic418967fa.accept_19_4_5_9_1_8855 42 62 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 62 161 (Polychromatic418967fa.accept_13_2_10_5_1_1643 41 62 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 62 161 (accept_3_2 40 62 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 62 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 62 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 62 161 (Polychromatic418967fa.accept_18_2_8_17_1_4754
  38 62 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 62 161 (accept_3_2 37
  62 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 62 161
  (Polychromatic418967fa.accept_10_6_2_1_1_494 36 62 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 62 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 62 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 62 161 (accept_3_2 34 62 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 62 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 62 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 62 161 (Polychromatic418967fa.accept_12_8_2_5_1_844
  32 62 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 62 161 (accept_3_2 31
  62 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 62 161
  (Polychromatic418967fa.accept_13_4_10_5_1_1644 30 62 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 62 161 (Polychromatic418967fa.accept_10_9_2_1_1_840 29 62 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 62 161 (accept_3_2 28 62 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 62 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 62 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 62 161 (Polychromatic418967fa.accept_10_6_2_1_1_494
  26 62 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 62 161 (accept_3_2 25
  62 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 62 161
  (Polychromatic418967fa.accept_15_9_2_11_1_2391 24 62 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 62 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 62 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 62 161 (accept_3_2 22 62 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 62 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 62 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 62 161 (Polychromatic418967fa.accept_12_8_2_5_1_844
  20 62 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 62 161 (accept_3_2 19
  62 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 62 161
  (Polychromatic418967fa.accept_17_1_11_8_1_2725 18 62 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 62 161 (Polychromatic418967fa.accept_13_4_10_5_1_1644 17 62 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 62 161 (accept_3_2 16 62 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 62 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 62 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 62 161
  (Polychromatic418967fa.accept_17_14_11_8_1_3854 14 62 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 62 161 (accept_3_2 13 62 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  62 161 (Polychromatic418967fa.accept_19_12_5_9_1_7320 12 62 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 62 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 62 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 62 161 (accept_3_2 10 62 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 62 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 62 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 62 161
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 62 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 62 161 (accept_3_2 7 62 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 62
  161 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 62 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 62 161 (Polychromatic418967fa.accept_15_5_2_11_1_1596 5 62 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 62 161 (accept_3_2 4 62 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 62 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 62 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 62 161 (Polychromatic418967fa.accept_13_2_10_5_1_1643
  2 62 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 161 (accept_3_2 1 62
  161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  161)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 161 (allA_of_3_0 61 61 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 60 161 (allA_succ_of_accept 59 60 161
  (Polychromatic418967fa.accept_9_5_6_8_1_101 59 60 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 60 161 (accept_3_2 58 60 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  60 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 60 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 60 161 (Polychromatic418967fa.accept_9_2_6_8_1_321 56 60 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 60 161 (accept_3_2 55 60 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 60 161 (Polychromatic418967fa.accept_21_12_18_14_1_8854 54 60 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 60 161
  (Polychromatic418967fa.accept_8_5_4_1_1_111 53 60 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 60 161 (accept_3_2 52 60 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  60 161 (Polychromatic418967fa.accept_13_12_8_5_1_976 51 60 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 60 161 (Polychromatic418967fa.accept_9_5_6_8_1_101 50 60 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 60 161 (accept_3_2 49 60 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 60 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 60 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 60 161
  (Polychromatic418967fa.accept_9_2_6_8_1_321 47 60 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 60 161 (accept_3_2 46 60 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  60 161 (Polychromatic418967fa.accept_8_5_4_1_1_111 45 60 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 60 161 (Polychromatic418967fa.accept_19_6_3_9_1_3332 44 60 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 161 (accept_3_2 43 60 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 60 161 (Polychromatic418967fa.accept_11_9_5_7_1_815 42 60 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 60 161
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 60 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 60 161 (accept_3_2 40 60 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  60 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 60 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 60 161 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 60 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 161 (accept_3_2 37 60 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 60 161 (Polychromatic418967fa.accept_13_10_8_5_1_1616 36 60 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 60 161
  (Polychromatic418967fa.accept_17_1_9_8_1_7492 35 60 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 60 161 (accept_3_2 34 60 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  60 161 (Polychromatic418967fa.accept_17_16_9_8_1_5063 33 60 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 60 161 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 60 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 161 (accept_3_2 31 60 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 60 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 60 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 60 161
  (Polychromatic418967fa.accept_8_5_4_1_1_111 29 60 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 60 161 (accept_3_2 28 60 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  60 161 (Polychromatic418967fa.accept_13_1_8_5_1_2315 27 60 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 60 161 (Polychromatic418967fa.accept_21_5_18_14_1_2793 26 60 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 60 161 (accept_3_2 25 60 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 60 161 (Polychromatic418967fa.accept_14_10_4_7_1_1214 24 60
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 60 161
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 60 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 60 161 (accept_3_2 22 60 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  60 161 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 60 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 60 161 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 60 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 161 (accept_3_2 19 60 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 60 161 (Polychromatic418967fa.accept_16_2_12_1_1_3086 18 60 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 60 161
  (Polychromatic418967fa.accept_14_3_4_7_1_175 17 60 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 60 161 (accept_3_2 16 60 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  60 161 (Polychromatic418967fa.accept_18_15_6_17_1_2386 15 60 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 60 161 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 60 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 161 (accept_3_2 13 60 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 60 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 60 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 60 161
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 60 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 60 161 (accept_3_2 10 60 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  60 161 (Polychromatic418967fa.accept_11_9_5_7_1_815 9 60 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 60 161 (Polychromatic418967fa.accept_16_8_12_1_1_7720 8 60 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 161 (accept_3_2 7 60 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 60 161 (Polychromatic418967fa.accept_17_6_9_8_1_6316 6 60 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 60 161
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 60 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 60 161 (accept_3_2 4 60 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 60
  161 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 60 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 60 161 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 60 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 161 (accept_3_2 1 60 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 60 161)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 161
  (allA_succ_of_accept 58 59 161 (accept_3_2 58 59 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  59 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 57 59 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 59 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 59 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 161 (accept_3_2 55 59 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 59 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 59 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 161
  (Polychromatic418967fa.accept_14_11_3_7_1_604 53 59 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 161 (accept_3_2 52 59 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 161 (Polychromatic418967fa.accept_9_6_5_8_1_598 51 59 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 59 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 161 (accept_3_2 49 59 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 59 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 161
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 59 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 161 (accept_3_2 46 59 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 161 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 59 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 161 (Polychromatic418967fa.accept_16_12_11_1_1_4088 44 59 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 161 (accept_3_2 43 59 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 59 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 161
  (Polychromatic418967fa.accept_11_8_4_7_1_1303 41 59 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 161 (accept_3_2 40 59 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 59 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 59 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 161 (accept_3_2 37 59 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 161 (Polychromatic418967fa.accept_11_3_4_7_1_114 36 59 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 161
  (Polychromatic418967fa.accept_10_5_9_1_1_187 35 59 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 161 (accept_3_2 34 59 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 161 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 59 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 161 (Polychromatic418967fa.accept_10_2_9_1_1_185 32 59 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 161 (accept_3_2 31 59 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 59 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 161
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 59 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 161 (accept_3_2 28 59 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 161 (Polychromatic418967fa.accept_15_12_14_11_1_4375 27 59 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 59 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 161 (accept_3_2 25 59 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 161 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 59 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 161
  (Polychromatic418967fa.accept_19_4_2_9_1_4584 23 59 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 161 (accept_3_2 22 59 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 59 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 59 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 161 (accept_3_2 19 59 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 59 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 161
  (Polychromatic418967fa.accept_19_17_2_9_1_4582 17 59 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 161 (accept_3_2 16 59 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 161 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 59 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 59 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 161 (accept_3_2 13 59 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 59 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 161
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 59 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 161 (accept_3_2 10 59 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 161 (Polychromatic418967fa.accept_21_9_17_14_1_603 9 59 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 161 (Polychromatic418967fa.accept_10_8_9_1_1_189 8 59 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 161 (accept_3_2 7 59 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 59 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 161
  (Polychromatic418967fa.accept_10_5_9_1_1_187 5 59 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 161 (accept_3_2 4 59 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  161 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 59 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 59 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 59 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 161 (accept_3_2 1 59 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 59 161))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 161 (allA_of_3_0
  58 58 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 57 161 (allA_succ_of_accept 56 57 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 57 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 161 (accept_3_2 55 57 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  57 161 (Polychromatic418967fa.accept_10_4_7_1_1_471 54 57 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 57 161 (Polychromatic418967fa.accept_11_9_2_7_1_1298 53 57 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 161 (accept_3_2 52 57 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 57 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 57 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 161 (accept_3_2 49 57 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  57 161 (Polychromatic418967fa.accept_14_6_1_7_1_2775 48 57 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 57 161 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 57 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 161 (accept_3_2 46 57 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 161 (Polychromatic418967fa.accept_16_13_9_1_1_3022 45 57 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 57 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 161 (accept_3_2 43 57 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  57 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 57 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 57 161 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 57 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 161 (accept_3_2 40 57 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 161 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 57 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 57 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 161 (accept_3_2 37 57 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  57 161 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 57 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 57 161 (Polychromatic418967fa.accept_24_11_9_17_1_8853 35 57 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 161 (accept_3_2 34 57 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 57 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 57 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 161 (accept_3_2 31 57 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  57 161 (Polychromatic418967fa.accept_20_10_17_1_1_8852 30 57 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 57 161 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 57 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 161 (accept_3_2 28 57 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 161 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 57 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 57 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 161 (accept_3_2 25 57 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  57 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 57 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 57 161 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 57 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 161 (accept_3_2 22 57 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 161 (Polychromatic418967fa.accept_16_5_9_1_1_2070 21 57 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 57 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 161 (accept_3_2 19 57 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  57 161 (Polychromatic418967fa.accept_16_2_9_1_1_6404 18 57 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 57 161 (Polychromatic418967fa.accept_21_17_15_14_1_5707 17 57 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 161 (accept_3_2 16 57 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 57 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 57 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 161 (accept_3_2 13 57 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  57 161 (Polychromatic418967fa.accept_21_12_15_14_1_8851 12 57 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 57 161 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 57 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 161 (accept_3_2 10 57 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 161 (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 57 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 57 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 161 (accept_3_2 7 57 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57
  161 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 57 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 161 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 57 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 161 (accept_3_2 4 57 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 161 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 57 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 57
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 161 (accept_3_2 1 57 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 161)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 161 (allA_succ_of_accept 55 56 161 (accept_3_2 55 56 161 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 56 161 (Polychromatic418967fa.accept_13_2_4_5_1_3152 54 56 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 56 161 (Polychromatic418967fa.accept_13_1_4_5_1_113 53 56 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 161 (accept_3_2 52 56 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 56 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 51
  56 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 56 161
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 56 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 49 56 161 7 7 8 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 48 56 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 56 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 56 161 (Polychromatic418967fa.accept_10_7_6_1_1_486 47 56 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 161 (accept_3_2 46 56 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 56 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 45
  56 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 161
  (Polychromatic418967fa.accept_16_12_8_1_1_5270 44 56 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 56 161 (accept_3_2 43 56 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 56
  161 7 6 8 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  56 161 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 56 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 56 161 (accept_3_2 40 56 161 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 56 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 56 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 161 (Polychromatic418967fa.accept_12_2_8_5_1_408 38 56 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 56 161 (accept_3_2 37 56 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 56 161 (Polychromatic418967fa.accept_13_10_4_5_1_2331
  36 56 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 56 161 7 5 8 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 56 161 (accept_3_2 34
  56 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 56 161
  (Polychromatic418967fa.accept_6_3_2_5_1_32 33 56 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 56 161 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 56 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 56 161 (accept_3_2 31 56 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 56 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 56 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 56 161 (Polychromatic418967fa.accept_17_12_5_8_1_7680
  29 56 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 56 161 7 4 8 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 56 161
  (Polychromatic418967fa.accept_6_3_2_5_1_32 27 56 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 56 161 (Polychromatic418967fa.accept_12_2_8_5_1_408 26 56 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 56 161 (accept_3_2 25 56 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 56 161 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 56 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 56 161 (Polychromatic418967fa.accept_9_5_2_8_1_109 23
  56 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 161 (accept_3_2 22 56
  161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 56 161 7 3 8 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 56 161
  (Polychromatic418967fa.accept_16_4_8_1_1_5257 20 56 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 56 161 (accept_3_2 19 56 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  56 161 (Polychromatic418967fa.accept_20_18_16_1_1_8850 18 56 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 56 161 (Polychromatic418967fa.accept_10_7_6_1_1_486 17 56 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 161 (accept_3_2 16 56 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 56 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 56 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 56 161 7 2 8 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 56 161 (accept_3_2 13 56 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 56 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 56 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 56 161
  (Polychromatic418967fa.accept_18_11_2_17_1_3490 11 56 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 56 161 (accept_3_2 10 56 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  56 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 56 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 56 161 (Polychromatic418967fa.accept_18_8_2_17_1_4782 8 56 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 56 161 7 1 8 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 56 161 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 56
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 56 161
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 56 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 56 161 (accept_3_2 4 56 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 56
  161 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 56 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 56 161 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 56 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 56 161 (accept_3_2 1 56 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 56 161)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 55 161 (allA_of_3_0 55
  55 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 54 161 (allA_succ_of_accept 53 54 161
  (Polychromatic418967fa.accept_16_5_6_1_1_2118 53 54 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 54 161 (accept_3_2 52 54 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  54 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 54 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 54 161 (Polychromatic418967fa.accept_15_5_9_11_1_4398 50 54 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 161 (accept_3_2 49 54 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 161 (Polychromatic418967fa.accept_13_9_2_5_1_2310 48 54 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 54 161
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 54 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 54 161 (accept_3_2 46 54 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  54 161 (Polychromatic418967fa.accept_10_5_4_1_1_842 45 54 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 54 161 (Polychromatic418967fa.accept_14_2_12_7_1_617 44 54 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 161 (accept_3_2 43 54 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 161 (Polychromatic418967fa.accept_13_3_2_5_1_1632 42 54 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 54 161
  (Polychromatic418967fa.accept_22_19_10_7_1_8849 41 54 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 54 161 (accept_3_2 40 54 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  54 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 54 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 54 161 (Polychromatic418967fa.accept_13_12_2_5_1_1634 38 54 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 161 (accept_3_2 37 54 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 54 161 (Polychromatic418967fa.accept_11_3_10_7_1_129 36 54 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 54 161
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 54 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 54 161 (accept_3_2 34 54 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  54 161 (Polychromatic418967fa.accept_13_7_2_5_1_2344 33 54 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 54 161 (Polychromatic418967fa.accept_15_2_9_11_1_1551 32 54 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 161 (accept_3_2 31 54 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 54 161 (Polychromatic418967fa.accept_13_4_2_5_1_4045 30 54 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 54 161
  (Polychromatic418967fa.accept_13_3_2_5_1_1632 29 54 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 54 161 (accept_3_2 28 54 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  54 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 54 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 54 161 (Polychromatic418967fa.accept_19_7_16_9_1_398 26 54 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 161 (accept_3_2 25 54 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 54 161 (Polychromatic418967fa.accept_21_3_12_14_1_8848 24 54 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 54 161
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 54 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 54 161 (accept_3_2 22 54 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  54 161 (Polychromatic418967fa.accept_15_6_9_11_1_858 21 54 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 54 161 (Polychromatic418967fa.accept_13_7_2_5_1_2344 20 54 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 161 (accept_3_2 19 54 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 54 161 (Polychromatic418967fa.accept_16_2_6_1_1_2069 18 54 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 54 161
  (Polychromatic418967fa.accept_10_7_4_1_1_1319 17 54 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 54 161 (accept_3_2 16 54 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  54 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 54 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 54 161 (Polychromatic418967fa.accept_11_3_10_7_1_129 14 54 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 161 (accept_3_2 13 54 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 54 161 (Polychromatic418967fa.accept_13_12_2_5_1_1634 12 54 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 54 161
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 54 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 54 161 (accept_3_2 10 54 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  54 161 (Polychromatic418967fa.accept_13_9_2_5_1_2310 9 54 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 54 161 (Polychromatic418967fa.accept_19_8_16_9_1_8847 8 54 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 161 (accept_3_2 7 54 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 54 161 (Polychromatic418967fa.accept_15_6_9_11_1_858 6 54 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 54 161
  (Polychromatic418967fa.accept_10_5_4_1_1_842 5 54 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 54 161 (accept_3_2 4 54 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 54
  161 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 54 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 54 161 (Polychromatic418967fa.accept_14_2_12_7_1_617 2 54 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 161 (accept_3_2 1 54 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 54 161)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 161
  (allA_succ_of_accept 52 53 161 (accept_3_2 52 53 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  53 161 (Polychromatic418967fa.accept_13_12_1_5_1_1650 51 53 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 53 161 (Polychromatic418967fa.accept_15_5_8_11_1_2350 50 53 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 161 (accept_3_2 49 53 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 53 161 (Polychromatic418967fa.accept_10_8_3_1_1_1316 48 53 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 161
  (Polychromatic418967fa.accept_13_8_1_5_1_3176 47 53 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 53 161 (accept_3_2 46 53 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  53 161 (Polychromatic418967fa.accept_13_6_1_5_1_3988 45 53 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 53 161 (Polychromatic418967fa.accept_8_4_5_1_1_299 44 53 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 161 (accept_3_2 43 53 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 53 161 (Polychromatic418967fa.accept_10_2_3_1_1_481 42 53 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 161
  (Polychromatic418967fa.accept_16_9_5_1_1_1259 41 53 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 161 (accept_3_2 40 53 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 161 (Polychromatic418967fa.accept_21_18_11_14_1_8846 39 53 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 161 (Polychromatic418967fa.accept_10_8_3_1_1_1316 38 53 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 161 (accept_3_2 37 53 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 161 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 53 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 161
  (Polychromatic418967fa.accept_11_2_9_7_1_124 35 53 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 161 (accept_3_2 34 53 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 161 (Polychromatic418967fa.accept_15_3_8_11_1_4386 33 53 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 161 (Polychromatic418967fa.accept_10_2_3_1_1_481 32 53 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 161 (accept_3_2 31 53 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 161 (Polychromatic418967fa.accept_13_4_1_5_1_1628 30 53 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 161
  (Polychromatic418967fa.accept_13_3_1_5_1_499 29 53 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 161 (accept_3_2 28 53 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 161 (Polychromatic418967fa.accept_11_5_9_7_1_411 27 53 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 161 (Polychromatic418967fa.accept_21_5_11_14_1_7219 26 53 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 161 (accept_3_2 25 53 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 161 (Polychromatic418967fa.accept_11_2_9_7_1_124 24 53 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 161
  (Polychromatic418967fa.accept_19_4_15_9_1_8845 23 53 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 161 (accept_3_2 22 53 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 161 (Polychromatic418967fa.accept_13_8_1_5_1_3176 21 53 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 161 (Polychromatic418967fa.accept_8_4_5_1_1_299 20 53 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 161 (accept_3_2 19 53 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 161 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 53 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 161
  (Polychromatic418967fa.accept_13_4_1_5_1_1628 17 53 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 161 (accept_3_2 16 53 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 161 (Polychromatic418967fa.accept_16_15_5_1_1_7724 15 53 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 161 (Polychromatic418967fa.accept_20_14_13_1_1_8844 14 53 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 161 (accept_3_2 13 53 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 161 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 53 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 161
  (Polychromatic418967fa.accept_17_11_2_8_1_7569 11 53 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 161 (accept_3_2 10 53 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 161 (Polychromatic418967fa.accept_13_9_1_5_1_964 9 53 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 161 (Polychromatic418967fa.accept_10_8_3_1_1_1316 8 53 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 161 (accept_3_2 7 53 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 161 (Polychromatic418967fa.accept_13_6_1_5_1_3988 6 53 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 161
  (Polychromatic418967fa.accept_11_5_9_7_1_411 5 53 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 161 (accept_3_2 4 53 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  161 (Polychromatic418967fa.accept_13_3_1_5_1_499 3 53 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 161 (Polychromatic418967fa.accept_10_2_3_1_1_481 2 53 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 161 (accept_3_2 1 53 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 161))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 161 (allA_of_3_0 52 52
  161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 161 (allA_succ_of_accept 50 51 161
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 51 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 161 (accept_3_2 49 51 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  51 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 51 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 51 161 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 51 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 161 (accept_3_2 46 51 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 161 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 51 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 51 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 161 (accept_3_2 43 51 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  51 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 51 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 51 161 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 51 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 161 (accept_3_2 40 51 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 51 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 161
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 51 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 161 (accept_3_2 37 51 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  51 161 (Polychromatic418967fa.accept_16_4_3_1_1_8843 36 51 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 51 161 (Polychromatic418967fa.accept_15_5_6_11_1_854 35 51 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 161 (accept_3_2 34 51 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 161 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 51 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 51 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 161 (accept_3_2 31 51 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  51 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 51 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 51 161 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 51 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 161 (accept_3_2 28 51 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 161 (Polychromatic418967fa.accept_13_1_12_5_1_1601 27 51 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 161
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 51 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 161 (accept_3_2 25 51 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  51 161 (Polychromatic418967fa.accept_15_9_6_11_1_1586 24 51 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 51 161 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 51 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 161 (accept_3_2 22 51 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 51 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 51 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 161 (accept_3_2 19 51 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  51 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 51 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 51 161 (Polychromatic418967fa.accept_13_4_12_5_1_476 17 51 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 161 (accept_3_2 16 51 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 161 (Polychromatic418967fa.accept_13_2_12_5_1_1602 15 51 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 161
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 51 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 161 (accept_3_2 13 51 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  51 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 51 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 51 161 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 51 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 161 (accept_3_2 10 51 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 161 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 51 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 51 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 161 (accept_3_2 7 51 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51
  161 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 51 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 161 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 51 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 161 (accept_3_2 4 51 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 51 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 51 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 51
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 161 (accept_3_2 1 51 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 161)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 161 (allA_succ_of_accept 49 50 161 (accept_3_2 49 50 161 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 50 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 50 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 50 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 50 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 161 (accept_3_2 46 50 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 50 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 45
  50 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 50 161
  (Polychromatic418967fa.accept_12_8_2_5_1_844 44 50 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 50 161 (accept_3_2 43 50 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  50 161 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 50 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 50 161 (Polychromatic418967fa.accept_14_13_8_7_1_1224 41 50 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 50 161 (accept_3_2 40 50 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 50 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 50 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 161
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 50 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 50 161 (accept_3_2 37 50 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  50 161 (Polychromatic418967fa.accept_15_6_5_11_1_2378 36 50 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 50 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 50 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 50 161 (accept_3_2 34 50 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 50 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 50 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 50 161
  (Polychromatic418967fa.accept_12_8_2_5_1_844 32 50 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 50 161 (accept_3_2 31 50 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  50 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 50 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 50 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 50 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 161 (accept_3_2 28 50 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 50 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 50 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 161
  (Polychromatic418967fa.accept_17_9_16_8_1_2721 26 50 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 50 161 (accept_3_2 25 50 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  50 161 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 50 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 50 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 50 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 161 (accept_3_2 22 50 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 50 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 50 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 50 161
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 50 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 50 161 (accept_3_2 19 50 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  50 161 (Polychromatic418967fa.accept_19_18_12_9_1_7315 18 50 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 50 161 (Polychromatic418967fa.accept_15_2_5_11_1_1563 17 50 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 161 (accept_3_2 16 50 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 50 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 50 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 50 161
  (Polychromatic418967fa.accept_17_14_16_8_1_3861 14 50 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 50 161 (accept_3_2 13 50 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  50 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 50 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 50 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 50 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 50 161 (accept_3_2 10 50 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 50 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 50 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 161
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 50 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 50 161 (accept_3_2 7 50 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50
  161 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 50 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 50 161 (Polychromatic418967fa.accept_19_5_12_9_1_4588 5 50 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 50 161 (accept_3_2 4 50 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 50 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 50 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 50
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 50 161 (accept_3_2 1 50 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 161)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  49 161 (allA_of_3_0 49 49 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 48 161 (allA_succ_of_accept 47 48
  161 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 48 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 48 161 (accept_3_2 46 48 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  48 161 (Polychromatic418967fa.accept_17_11_14_8_1_2729 45 48 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 48 161 (Polychromatic418967fa.accept_15_14_3_11_1_850 44 48 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 161 (accept_3_2 43 48 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 48 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 48 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 48 161
  (Polychromatic418967fa.accept_9_5_3_8_1_316 41 48 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 48 161 (accept_3_2 40 48 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  48 161 (Polychromatic418967fa.accept_10_9_8_1_1_1331 39 48 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 48 161 (Polychromatic418967fa.accept_9_2_3_8_1_318 38 48 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 161 (accept_3_2 37 48 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 161 (Polychromatic418967fa.accept_11_3_4_7_1_114 36 48 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 48 161
  (Polychromatic418967fa.accept_19_16_10_9_1_8842 35 48 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 48 161 (accept_3_2 34 48 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  48 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 48 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 48 161 (Polychromatic418967fa.accept_9_5_3_8_1_316 32 48 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 161 (accept_3_2 31 48 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 161 (Polychromatic418967fa.accept_11_8_4_7_1_1303 30 48 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 48 161
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 48 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 48 161 (accept_3_2 28 48 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  48 161 (Polychromatic418967fa.accept_13_1_9_5_1_1598 27 48 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 48 161 (Polychromatic418967fa.accept_19_7_10_9_1_2162 26 48 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 161 (accept_3_2 25 48 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 48 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 48 161
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 48 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 48 161 (accept_3_2 22 48 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  48 161 (Polychromatic418967fa.accept_15_6_3_11_1_848 21 48 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 48 161 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 48 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 161 (accept_3_2 19 48 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 48 161 (Polychromatic418967fa.accept_19_18_10_9_1_5996 18 48 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 48 161
  (Polychromatic418967fa.accept_13_4_9_5_1_1641 17 48 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 48 161 (accept_3_2 16 48 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  48 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 48 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 48 161 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 48 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 161 (accept_3_2 13 48 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 48 161 (Polychromatic418967fa.accept_19_12_10_9_1_3326 12 48 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 48 161
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 48 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 48 161 (accept_3_2 10 48 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  48 161 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 48 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 48 161 (Polychromatic418967fa.accept_11_8_4_7_1_1303 8 48 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 161 (accept_3_2 7 48 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 48 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 48 161
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 48 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 48 161 (accept_3_2 4 48 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 48
  161 (Polychromatic418967fa.accept_10_3_8_1_1_182 3 48 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 48 161 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 48 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 161 (accept_3_2 1 48 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 48 161)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 161 (allA_succ_of_accept 46
  47 161 (accept_3_2 46 47 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 161
  (Polychromatic418967fa.accept_25_20_22_11_1_8841 45 47 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 47 161 (Polychromatic418967fa.accept_10_4_7_1_1_471 44 47 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 161 (accept_3_2 43 47 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 47 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 47 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 161
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 47 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 47 161 (accept_3_2 40 47 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  47 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 47 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 47 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 47 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 161 (accept_3_2 37 47 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 47 161 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 47 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 161
  (Polychromatic418967fa.accept_15_5_2_11_1_1596 35 47 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 161 (accept_3_2 34 47 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 161 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 47 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 161 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 47 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 161 (accept_3_2 31 47 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 47 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 161
  (Polychromatic418967fa.accept_13_3_8_5_1_974 29 47 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 161 (accept_3_2 28 47 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 161 (Polychromatic418967fa.accept_13_1_8_5_1_2315 27 47 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 47 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 161 (accept_3_2 25 47 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 161 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 47 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 161
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 47 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 161 (accept_3_2 22 47 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 47 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 161 (Polychromatic418967fa.accept_15_5_2_11_1_1596 20 47 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 161 (accept_3_2 19 47 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 47 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 161
  (Polychromatic418967fa.accept_21_17_5_14_1_4144 17 47 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 161 (accept_3_2 16 47 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 161 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 47 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 47 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 161 (accept_3_2 13 47 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 47 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 161
  (Polychromatic418967fa.accept_16_11_15_1_1_2074 11 47 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 161 (accept_3_2 10 47 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 161 (Polychromatic418967fa.accept_14_9_5_7_1_1251 9 47 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 161 (Polychromatic418967fa.accept_16_8_15_1_1_3006 8 47 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 161 (accept_3_2 7 47 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 47 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 161
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 47 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 161 (accept_3_2 4 47 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  161 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 47 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 47 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 161 (accept_3_2 1 47 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 161))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 161 (allA_of_3_0 46 46 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 45 161 (allA_succ_of_accept 44 45 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 45 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 161 (accept_3_2 43 45 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  45 161 (Polychromatic418967fa.accept_13_3_6_5_1_2336 42 45 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 45 161 (Polychromatic418967fa.accept_16_9_13_1_1_3069 41 45 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 161 (accept_3_2 40 45 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 161 (Polychromatic418967fa.accept_10_9_5_1_1_1325 39 45 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 45 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 161 (accept_3_2 37 45 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  45 161 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 45 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 45 161 (Polychromatic418967fa.accept_16_3_13_1_1_1206 35 45 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 161 (accept_3_2 34 45 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 161 (Polychromatic418967fa.accept_18_15_9_17_1_6043 33 45
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 45 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 161 (accept_3_2 31 45 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  45 161 (Polychromatic418967fa.accept_13_4_6_5_1_2333 30 45 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 45 161 (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 45 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 161 (accept_3_2 28 45 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 161 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 45 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 45 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 161 (accept_3_2 25 45 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  45 161 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 45 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 45 161 (Polychromatic418967fa.accept_13_10_6_5_1_2297 23 45 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 161 (accept_3_2 22 45 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 161 (Polychromatic418967fa.accept_16_5_13_1_1_2084 21 45
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 45 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 45 161 (accept_3_2 19 45 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  45 161 (Polychromatic418967fa.accept_14_4_3_7_1_3702 18 45 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 45 161 (Polychromatic418967fa.accept_11_6_1_7_1_1315 17 45 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 161 (accept_3_2 16 45 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 161 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 45 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 45 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 161 (accept_3_2 13 45 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  45 161 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 45 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 45 161 (Polychromatic418967fa.accept_13_11_6_5_1_2339 11 45 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 161 (accept_3_2 10 45 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 161 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 45 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 45 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 161 (accept_3_2 7 45 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45
  161 (Polychromatic418967fa.accept_10_6_5_1_1_482 6 45 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 161 (Polychromatic418967fa.accept_16_5_13_1_1_2084 5 45 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 161 (accept_3_2 4 45 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 45 161 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 45 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 45
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 161 (accept_3_2 1 45 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 161))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  161 (allA_succ_of_accept 43 44 161 (accept_3_2 43 44 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 44 161 (Polychromatic418967fa.accept_15_12_14_11_1_4375 42 44 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 44 161 (Polychromatic418967fa.accept_18_5_8_17_1_3478 41 44 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 161 (accept_3_2 40 44 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 44 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 44 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 161
  (Polychromatic418967fa.accept_12_2_8_5_1_408 38 44 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 44 161 (accept_3_2 37 44 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  44 161 (Polychromatic418967fa.accept_16_4_12_1_1_1204 36 44 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 44 161 (Polychromatic418967fa.accept_10_5_4_1_1_842 35 44 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 161 (accept_3_2 34 44 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 44 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 44 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 44 161
  (Polychromatic418967fa.accept_17_15_10_8_1_1708 32 44 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 44 161 (accept_3_2 31 44 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  44 161 (Polychromatic418967fa.accept_20_10_4_1_1_8840 30 44 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 44 161 (Polychromatic418967fa.accept_8_5_4_1_1_111 29 44 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 44 161 (accept_3_2 28 44 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 44 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 44 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 44 161
  (Polychromatic418967fa.accept_12_2_8_5_1_408 26 44 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 44 161 (accept_3_2 25 44 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  44 161 (Polychromatic418967fa.accept_16_8_12_1_1_7720 24 44 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 44 161 (Polychromatic418967fa.accept_14_9_2_7_1_1242 23 44 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 44 161 (accept_3_2 22 44 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 44 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 44 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 44 161
  (Polychromatic418967fa.accept_16_4_12_1_1_1204 20 44 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 44 161 (accept_3_2 19 44 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  44 161 (Polychromatic418967fa.accept_15_3_14_11_1_1579 18 44 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 44 161 (Polychromatic418967fa.accept_10_7_4_1_1_1319 17 44 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 44 161 (accept_3_2 16 44 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 44 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 44 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 44 161
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 44 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 44 161 (accept_3_2 13 44 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  44 161 (Polychromatic418967fa.accept_14_12_2_7_1_1243 12 44 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 44 161 (Polychromatic418967fa.accept_16_11_12_1_1_3001 11 44 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 44 161 (accept_3_2 10 44 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 44 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 44 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 44 161
  (Polychromatic418967fa.accept_16_8_12_1_1_7720 8 44 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 44 161 (accept_3_2 7 44 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 44
  161 (Polychromatic418967fa.accept_21_6_2_14_1_5688 6 44 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 44 161 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 44 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 44 161 (accept_3_2 4 44 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 44 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 44 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 44 161
  (Polychromatic418967fa.accept_12_2_8_5_1_408 2 44 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 44 161 (accept_3_2 1 44 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44
  161)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 161 (allA_of_3_0 43 43 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 42 161 (allA_succ_of_accept 41 42 161 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 42 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 42 161 (accept_3_2 40 42 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 42 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 39
  42 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 42 161
  (Polychromatic418967fa.accept_9_2_6_8_1_321 38 42 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 42 161 (accept_3_2 37 42 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  42 161 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 42 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 42 161 7 5 6 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 34 42 161 (accept_3_2 34 42 161 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 42 161 (Polychromatic418967fa.accept_10_3_2_1_1_839 33 42 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 42 161 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 42 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 161 (accept_3_2 31 42 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 42 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 30
  42 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 42 161
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 42 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 42 161 7 4 6 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 42 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 42 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 42 161 (Polychromatic418967fa.accept_10_6_2_1_1_494 26 42 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 161 (accept_3_2 25 42 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 161 (Polychromatic418967fa.accept_11_2_9_7_1_124
  24 42 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 42 161
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 42 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 42 161 (accept_3_2 22 42 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 42
  161 7 3 6 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20
  42 161 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 42 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 42 161 (accept_3_2 19 42 161 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 42 161 (Polychromatic418967fa.accept_26_18_16_5_1_8839 18 42 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 42 161 (Polychromatic418967fa.accept_27_17_15_26_1_8838 17 42
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 42 161 (accept_3_2 16 42 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 42 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 15
  42 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 42 161 7 2 6 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 161 (accept_3_2 13
  42 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 161
  (Polychromatic418967fa.accept_9_3_6_8_1_308 12 42 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 42 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 42 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 42 161 (accept_3_2 10 42 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 42 161 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 42 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 42 161 (Polychromatic418967fa.accept_13_8_3_5_1_1636 8
  42 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 42 161 7 1 6 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 42 161
  (Polychromatic418967fa.accept_10_6_2_1_1_494 6 42 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 42 161 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 42 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42 161 (accept_3_2 4 42 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 42 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 42 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 42 161 (Polychromatic418967fa.accept_9_2_6_8_1_321 2
  42 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 161 (accept_3_2 1 42 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42 161)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 161
  (allA_succ_of_accept 40 41 161 (accept_3_2 40 41 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  41 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 41 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 41 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 41 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 161 (accept_3_2 37 41 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 41 161 (Polychromatic418967fa.accept_13_10_2_5_1_1633 36 41 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 161
  (Polychromatic418967fa.accept_13_9_2_5_1_2310 35 41 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 41 161 (accept_3_2 34 41 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  41 161 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 41 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 41 161 (Polychromatic418967fa.accept_19_13_3_9_1_5980 32 41 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 161 (accept_3_2 31 41 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 41 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 41 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 161
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 41 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 161 (accept_3_2 28 41 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 161 (Polychromatic418967fa.accept_21_6_20_14_1_8837 27 41 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 161 (Polychromatic418967fa.accept_11_4_8_7_1_819 26 41 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 161 (accept_3_2 25 41 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 161 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 41 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 161
  (Polychromatic418967fa.accept_13_10_2_5_1_1633 23 41 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 161 (accept_3_2 22 41 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 41 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 41 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 161 (accept_3_2 19 41 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 161 (Polychromatic418967fa.accept_16_2_9_1_1_6404 18 41 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 161
  (Polychromatic418967fa.accept_13_4_2_5_1_4045 17 41 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 161 (accept_3_2 16 41 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 161 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 41 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 161 (Polychromatic418967fa.accept_17_14_7_8_1_7544 14 41 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 161 (accept_3_2 13 41 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 41 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 161
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 41 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 161 (accept_3_2 10 41 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 161 (Polychromatic418967fa.accept_13_9_2_5_1_2310 9 41 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 161 (Polychromatic418967fa.accept_14_8_13_7_1_2798 8 41 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 161 (accept_3_2 7 41 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 161 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 41 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 161
  (Polychromatic418967fa.accept_16_5_9_1_1_2070 5 41 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 161 (accept_3_2 4 41 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  161 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 41 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 41 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 161 (accept_3_2 1 41 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 161))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 161 (allA_of_3_0 40 40 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 161 (allA_succ_of_accept 38 39 161
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 39 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 161 (accept_3_2 37 39 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 161 (Polychromatic418967fa.accept_15_6_9_11_1_858 36 39 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 161 (Polychromatic418967fa.accept_10_5_9_1_1_187 35 39 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 161 (accept_3_2 34 39 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 39 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 39 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 161 (accept_3_2 31 39 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 39 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 161 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 39 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 161 (accept_3_2 28 39 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 161 (Polychromatic418967fa.accept_19_8_1_9_1_7329 27 39 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 161
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 39 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 161 (accept_3_2 25 39 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 39 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 161 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 39 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 161 (accept_3_2 22 39 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 161 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 39 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 39 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 161 (accept_3_2 19 39 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 39 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 161 (Polychromatic418967fa.accept_14_3_11_7_1_1260 17 39 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 161 (accept_3_2 16 39 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 39 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 161
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 39 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 161 (accept_3_2 13 39 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  39 161 (Polychromatic418967fa.accept_10_2_9_1_1_185 12 39 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 161 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 39 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 161 (accept_3_2 10 39 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 161 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 39 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 39 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 161 (accept_3_2 7 39 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  161 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 39 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 161 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 39 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 161 (accept_3_2 4 39 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 161 (Polychromatic418967fa.accept_14_3_11_7_1_1260 3 39 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 39
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 161 (accept_3_2 1 39 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 161))))))))))))))))))))))))))))))))))))))) (allB_succ 38 161
  (allA_succ_of_accept 37 38 161 (accept_3_2 37 38 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  38 161 (Polychromatic418967fa.accept_20_16_18_1_1_8836 36 38 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 38 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 38 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 161 (accept_3_2 34 38 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 38 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 161
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 38 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 38 161 (accept_3_2 31 38 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  38 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 38 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 38 161 (Polychromatic418967fa.accept_10_9_8_1_1_1331 29 38 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 161 (accept_3_2 28 38 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 38 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 38 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 161
  (Polychromatic418967fa.accept_18_8_2_17_1_4782 26 38 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 38 161 (accept_3_2 25 38 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  38 161 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 38 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 38 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 38 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 161 (accept_3_2 22 38 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 38 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 161
  (Polychromatic418967fa.accept_11_9_5_7_1_815 20 38 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 38 161 (accept_3_2 19 38 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  38 161 (Polychromatic418967fa.accept_14_4_10_7_1_1946 18 38 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 38 161 (Polychromatic418967fa.accept_13_4_12_5_1_476 17 38 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 161 (accept_3_2 16 38 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 38 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 161
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 38 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 38 161 (accept_3_2 13 38 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  38 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 38 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 38 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 38 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 161 (accept_3_2 10 38 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 38 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 161
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 38 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 161 (accept_3_2 7 38 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  161 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 38 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 38 161 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 38 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 161 (accept_3_2 4 38 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 38 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 38 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 161 (Polychromatic418967fa.accept_13_2_12_5_1_1602
  2 38 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 161 (accept_3_2 1 38
  161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 161)))))))))))))))))))))))))))))))))))))) (allB_succ 37 161
  (allA_of_3_0 37 37 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 36 161 (allA_succ_of_accept 35 36 161
  (Polychromatic418967fa.accept_10_5_6_1_1_836 35 36 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 36 161 (accept_3_2 34 36 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  36 161 (Polychromatic418967fa.accept_15_3_6_11_1_855 33 36 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 36 161 (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 36 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 161 (accept_3_2 31 36 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 36 161 (Polychromatic418967fa.accept_13_4_10_5_1_1644 30 36 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 36 161
  (Polychromatic418967fa.accept_8_5_4_1_1_111 29 36 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 36 161 (accept_3_2 28 36 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  36 161 (Polychromatic418967fa.accept_10_7_6_1_1_486 27 36 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 36 161 (Polychromatic418967fa.accept_11_4_3_7_1_828 26 36 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 161 (accept_3_2 25 36 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 36 161 (Polychromatic418967fa.accept_15_9_6_11_1_1586 24 36 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 36 161
  (Polychromatic418967fa.accept_28_23_8_21_1_8835 23 36 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 36 161 (accept_3_2 22 36 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  36 161 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 36 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 36 161 (Polychromatic418967fa.accept_14_6_8_7_1_589 20 36 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 161 (accept_3_2 19 36 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 161 (Polychromatic418967fa.accept_15_3_6_11_1_855 18 36 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 36 161
  (Polychromatic418967fa.accept_10_7_6_1_1_486 17 36 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 36 161 (accept_3_2 16 36 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  36 161 (Polychromatic418967fa.accept_10_5_6_1_1_836 15 36 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 36 161 (Polychromatic418967fa.accept_16_14_4_1_1_3049 14 36 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 161 (accept_3_2 13 36 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 36 161 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 36 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 36 161
  (Polychromatic418967fa.accept_17_11_2_8_1_7569 11 36 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 36 161 (accept_3_2 10 36 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  36 161 (Polychromatic418967fa.accept_15_9_6_11_1_1586 9 36 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 36 161 (Polychromatic418967fa.accept_13_8_10_5_1_977 8 36 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 161 (accept_3_2 7 36 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 36 161 (Polychromatic418967fa.accept_13_6_10_5_1_1648 6 36 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 36 161
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 36 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 36 161 (accept_3_2 4 36 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 36
  161 (Polychromatic418967fa.accept_15_3_6_11_1_855 3 36 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 36 161 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 36 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 161 (accept_3_2 1 36 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 36 161)))))))))))))))))))))))))))))))))))) (allB_succ 35 161 (allA_succ_of_accept 34 35
  161 (accept_3_2 34 35 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 161
  (Polychromatic418967fa.accept_19_14_16_9_1_8834 33 35 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 161 (Polychromatic418967fa.accept_15_2_5_11_1_1563 32 35 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 161 (accept_3_2 31 35 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 35 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 35 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 161 (Polychromatic418967fa.accept_10_9_5_1_1_1325
  29 35 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 35 161 7 4 5 23 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 35 161
  (Polychromatic418967fa.accept_13_1_9_5_1_1598 27 35 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 35 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 35 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 161 (accept_3_2 25 35 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 35 161 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 35 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 161 (Polychromatic418967fa.accept_15_8_5_11_1_2358
  23 35 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 161 (accept_3_2 22
  35 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 35 161 7 3 5 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 35 161
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 20 35 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 35 161 (accept_3_2 19 35 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  35 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 35 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 35 161 (Polychromatic418967fa.accept_13_4_9_5_1_1641 17 35 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 161 (accept_3_2 16 35 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 161 (Polychromatic418967fa.accept_13_2_9_5_1_959 15 35 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 35 161 7 2 5 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 35 161 (accept_3_2 13 35 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 161 (Polychromatic418967fa.accept_19_12_16_9_1_5976 12 35
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 161
  (Polychromatic418967fa.accept_17_11_1_8_1_7502 11 35 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 35 161 (accept_3_2 10 35 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  35 161 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 35 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 35 161 (Polychromatic418967fa.accept_15_8_5_11_1_2358 8 35 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 35 161 7 1 5 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 35 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 35
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 161
  (Polychromatic418967fa.accept_20_5_15_1_1_7278 5 35 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 35 161 (accept_3_2 4 35 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35
  161 (Polychromatic418967fa.accept_13_3_9_5_1_2340 3 35 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 35 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 35 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 161 (accept_3_2 1 35 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 35 161))))))))))))))))))))))))))))))))))) (allB_succ 34 161 (allA_of_3_0 34 34 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 33 161 (allA_succ_of_accept 32 33 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 33 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 161 (accept_3_2 31 33 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  33 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 33 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 33 161 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 33 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 161 (accept_3_2 28 33 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 161 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 33 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 33 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 161 (accept_3_2 25 33 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  33 161 (Polychromatic418967fa.accept_13_11_7_5_1_2314 24 33 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 33 161 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 33 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 161 (accept_3_2 22 33 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 33 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 33 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 33 161 (accept_3_2 19 33 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  33 161 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 33 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 33 161 (Polychromatic418967fa.accept_19_17_14_9_1_8833 17 33 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 161 (accept_3_2 16 33 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 161 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 33 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 33 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 161 (accept_3_2 13 33 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  33 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 33 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 33 161 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 33 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 161 (accept_3_2 10 33 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 161 (Polychromatic418967fa.accept_14_9_5_7_1_1251 9 33 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 33 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 161 (accept_3_2 7 33 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33
  161 (Polychromatic418967fa.accept_15_6_3_11_1_848 6 33 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 33 161 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 33 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 161 (accept_3_2 4 33 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 33 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 33 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 33 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 33 161 (accept_3_2 1 33 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33
  161))))))))))))))))))))))))))))))))) (allB_succ 32 161 (allA_succ_of_accept 31 32 161 (accept_3_2 31 32 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 32 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 32 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 32 161
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 32 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 32 161 (accept_3_2 28 32 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  32 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 32 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 32 161 (Polychromatic418967fa.accept_10_6_2_1_1_494 26 32 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 32 161 (accept_3_2 25 32 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 32 161 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 32 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 32 161
  (Polychromatic418967fa.accept_10_3_2_1_1_839 23 32 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 32 161 (accept_3_2 22 32 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  32 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 32 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 32 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 32 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 32 161 (accept_3_2 19 32 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 32 161 (Polychromatic418967fa.accept_19_18_13_9_1_5971 18 32 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 32 161
  (Polychromatic418967fa.accept_13_4_6_5_1_2333 17 32 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 32 161 (accept_3_2 16 32 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  32 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 32 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 32 161 (Polychromatic418967fa.accept_11_3_10_7_1_129 14 32 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 32 161 (accept_3_2 13 32 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 32 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 32 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 32 161
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 32 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 32 161 (accept_3_2 10 32 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  32 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 32 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 32 161 (Polychromatic418967fa.accept_21_8_11_14_1_5665 8 32 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 32 161 (accept_3_2 7 32 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 32 161 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 32 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 32 161
  (Polychromatic418967fa.accept_15_5_2_11_1_1596 5 32 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 32 161 (accept_3_2 4 32 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 32
  161 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 32 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 32 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 32 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 161 (accept_3_2 1 32 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 32 161)))))))))))))))))))))))))))))))) (allB_succ 31 161 (allA_of_3_0 31 31 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 30 161 (allA_succ_of_accept 29 30 161
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 30 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 30 161 (accept_3_2 28 30 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  30 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 30 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 30 161 (Polychromatic418967fa.accept_11_4_8_7_1_819 26 30 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 30 161 (accept_3_2 25 30 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 30 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 30 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 30 161
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 30 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 30 161 (accept_3_2 22 30 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  30 161 (Polychromatic418967fa.accept_17_4_13_8_1_3874 21 30 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 30 161 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 30 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 161 (accept_3_2 19 30 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 161 (Polychromatic418967fa.accept_21_18_9_14_1_8832 18 30 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 30 161
  (Polychromatic418967fa.accept_19_17_11_9_1_2141 17 30 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 30 161 (accept_3_2 16 30 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  30 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 30 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 30 161 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 30 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 161 (accept_3_2 13 30 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 161 (Polychromatic418967fa.accept_13_12_4_5_1_1637 12 30 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 30 161
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 30 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 30 161 (accept_3_2 10 30 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  30 161 (Polychromatic418967fa.accept_13_9_4_5_1_1651 9 30 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 30 161 (Polychromatic418967fa.accept_19_8_11_9_1_8827 8 30 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 161 (accept_3_2 7 30 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 30 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 30 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 30 161
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 30 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 30 161 (accept_3_2 4 30 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 30
  161 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 30 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 30 161 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 30 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 161 (accept_3_2 1 30 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 30 161)))))))))))))))))))))))))))))) (allB_succ 29 161 (allA_succ_of_accept 28 29 161
  (accept_3_2 28 29 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 161
  (Polychromatic418967fa.accept_13_1_3_5_1_140 27 29 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 161 (Polychromatic418967fa.accept_19_7_10_9_1_2162 26 29 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 161 (accept_3_2 25 29 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 161 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 29 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 161 (Polychromatic418967fa.accept_9_5_2_8_1_109 23
  29 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 161 (accept_3_2 22 29
  161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 161
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 29 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 29 161 (Polychromatic418967fa.accept_8_4_5_1_1_299 20 29 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 161 (accept_3_2 19 29 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 29 161 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 29 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 161
  (Polychromatic418967fa.accept_21_17_8_14_1_5638 17 29 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 161 (accept_3_2 16 29 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  29 161 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 29 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 29 161 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 29 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 161 (accept_3_2 13 29 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 161 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 29 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 161
  (Polychromatic418967fa.accept_13_11_3_5_1_982 11 29 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 161 (accept_3_2 10 29 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  29 161 (Polychromatic418967fa.accept_13_9_3_5_1_1605 9 29 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 29 161 (Polychromatic418967fa.accept_10_8_9_1_1_189 8 29 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 161 (accept_3_2 7 29 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 161 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 29 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 161
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 29 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 161 (accept_3_2 4 29 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  161 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 29 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 161 (Polychromatic418967fa.accept_10_2_9_1_1_185 2 29 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 161 (accept_3_2 1 29 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 161))))))))))))))))))))))))))))) (allB_succ 28 161 (allA_of_3_0 28 28 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 27 161 (allA_succ_of_accept 26 27 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 27
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 161 (accept_3_2 25 27 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 161 (Polychromatic418967fa.accept_10_4_7_1_1_471
  24 27 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 161
  (Polychromatic418967fa.accept_15_8_12_11_1_1570 23 27 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 27 161 (accept_3_2 22 27 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  27 161 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 27 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 27 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 27 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 161 (accept_3_2 19 27 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 27 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 27 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 161
  (Polychromatic418967fa.accept_13_4_1_5_1_1628 17 27 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 27 161 (accept_3_2 16 27 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  27 161 (Polychromatic418967fa.accept_14_1_13_7_1_1205 15 27 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 27 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 27 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 161 (accept_3_2 13 27 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 27 161 (Polychromatic418967fa.accept_13_12_1_5_1_1650 12 27 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 161
  (Polychromatic418967fa.accept_19_11_8_9_1_5993 11 27 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 27 161 (accept_3_2 10 27 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  27 161 (Polychromatic418967fa.accept_11_9_5_7_1_815 9 27 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 27 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 27 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 161 (accept_3_2 7 27 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 27 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 27 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 161
  (Polychromatic418967fa.accept_28_5_27_21_1_8831 5 27 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 27 161 (accept_3_2 4 27 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27
  161 (Polychromatic418967fa.accept_13_3_1_5_1_499 3 27 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 27 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 27 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 161 (accept_3_2 1 27 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 27 161))))))))))))))))))))))))))) (allB_succ 26 161 (allA_succ_of_accept 25 26 161 (accept_3_2
  25 26 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 26 161
  (Polychromatic418967fa.accept_19_5_7_9_1_5954 24 26 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 26 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 26 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 26 161 (accept_3_2 22 26 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 26 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 26 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 26 161 (Polychromatic418967fa.accept_12_8_2_5_1_844
  20 26 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 26 161 (accept_3_2 19
  26 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 26 161
  (Polychromatic418967fa.accept_17_1_9_8_1_7492 18 26 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 26 161 (Polychromatic418967fa.accept_10_7_6_1_1_486 17 26 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 26 161 (accept_3_2 16 26 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 26 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 26 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 26 161 (Polychromatic418967fa.accept_11_3_4_7_1_114
  14 26 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 26 161 (accept_3_2 13
  26 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 26 161
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 26 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 26 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 26 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 26 161 (accept_3_2 10 26 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 26 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 26 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 26 161 (Polychromatic418967fa.accept_11_8_4_7_1_1303 8
  26 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 26 161 (accept_3_2 7 26 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 26 161 (Polychromatic418967fa.accept_17_6_9_8_1_6316 6
  26 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 26 161
  (Polychromatic418967fa.accept_10_5_6_1_1_836 5 26 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 26 161 (accept_3_2 4 26 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 26
  161 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 26 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 26 161 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 26 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 26 161 (accept_3_2 1 26 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 26 161)))))))))))))))))))))))))) (allB_succ 25 161 (allA_of_3_0 25 25 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 24 161 (allA_succ_of_accept 23 24 161 (Polychromatic418967fa.accept_9_5_6_8_1_101 23
  24 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 161 (accept_3_2 22 24
  161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 24 161
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 24 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 24 161 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 24 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 24 161 (accept_3_2 19 24 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 24 161 (Polychromatic418967fa.accept_14_4_10_7_1_1946 18 24 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 24 161
  (Polychromatic418967fa.accept_10_7_4_1_1_1319 17 24 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 24 161 (accept_3_2 16 24 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  24 161 (Polychromatic418967fa.accept_10_5_4_1_1_842 15 24 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 24 161 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 24 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 161 (accept_3_2 13 24 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 24 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 24 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 24 161
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 24 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 24 161 (accept_3_2 10 24 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  24 161 (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 24 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 24 161 (Polychromatic418967fa.accept_21_8_3_14_1_4165 8 24 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 161 (accept_3_2 7 24 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 24 161 (Polychromatic418967fa.accept_13_6_11_5_1_133 6 24 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 24 161
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 24 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 24 161 (accept_3_2 4 24 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 24
  161 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 24 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 24 161 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 24 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 24 161 (accept_3_2 1 24 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 24 161)))))))))))))))))))))))) (allB_succ 23 161 (allA_succ_of_accept 22 23 161 (accept_3_2 22
  23 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 161
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 23 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 23 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 161 (accept_3_2 19 23 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 23 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 161 (Polychromatic418967fa.accept_11_6_1_7_1_1315
  17 23 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 161 (accept_3_2 16
  23 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 161
  (Polychromatic418967fa.accept_9_6_5_8_1_598 15 23 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 23 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 23 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 161 (accept_3_2 13 23 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 23 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 23 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 161 (Polychromatic418967fa.accept_9_2_5_8_1_11 11
  23 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 161 (accept_3_2 10 23
  161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 161
  (Polychromatic418967fa.accept_17_9_6_8_1_6315 9 23 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 23 161 (Polychromatic418967fa.accept_10_8_3_1_1_1316 8 23 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 161 (accept_3_2 7 23 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 23 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 23 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 161 (Polychromatic418967fa.accept_14_5_9_7_1_590 5
  23 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 161 (accept_3_2 4 23 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 23
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 161
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 23 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 23 161 (accept_3_2 1 23 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23
  161))))))))))))))))))))))) (allB_succ 22 161 (allA_of_3_0 22 22 161 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 21 161 (allA_succ_of_accept 20 21 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 21 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 161 (accept_3_2 19 21 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 161 (Polychromatic418967fa.accept_15_3_6_11_1_855 18 21 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 161
  (Polychromatic418967fa.accept_15_2_6_11_1_1587 17 21 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 161 (accept_3_2 16 21 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  21 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 21 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 21 161 7 2 3 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 21 161 (accept_3_2 13 21 161 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 21 161 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 21 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 161 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 21 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 161 (accept_3_2 10 21 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 161 (Polychromatic418967fa.accept_15_9_6_11_1_1586
  9 21 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 21 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 21 161 7 1 3 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 21 161 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 21 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 161 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 21 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 161 (accept_3_2 4 21 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21 161 (Polychromatic418967fa.accept_11_3_10_7_1_129 3
  21 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 21 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 21 161 (accept_3_2 1 21 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21
  161))))))))))))))))))))) (allB_succ 20 161 (allA_succ_of_accept 19 20 161 (accept_3_2 19 20 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 20 161 (Polychromatic418967fa.accept_21_18_20_14_1_5711 18 20 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 20 161
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 17 20 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 20 161 (accept_3_2 16 20 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  20 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 20 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 20 161 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 20 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 20 161 (accept_3_2 13 20 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 20 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 20 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 20 161
  (Polychromatic418967fa.accept_13_11_7_5_1_2314 11 20 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 20 161 (accept_3_2 10 20 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  20 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 20 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 20 161 (Polychromatic418967fa.accept_14_8_6_7_1_1934 8 20 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 20 161 (accept_3_2 7 20 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 20 161 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 20 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 20 161
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 20 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 20 161 (accept_3_2 4 20 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 20
  161 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 20 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 20 161 (Polychromatic418967fa.accept_11_2_9_7_1_124 2 20 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 20 161 (accept_3_2 1 20 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 161)))))))))))))))))))) (allB_succ 19 161 (allA_of_3_0 19 19 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 18 161 (allA_succ_of_accept 17 18 161 (Polychromatic418967fa.accept_14_3_4_7_1_175 17 18 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 161 (accept_3_2 16 18 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 18 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 15
  18 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 161
  (Polychromatic418967fa.accept_15_14_3_11_1_850 14 18 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 18 161 (accept_3_2 13 18 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  18 161 (Polychromatic418967fa.accept_16_12_2_1_1_1215 12 18 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 18 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 18 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 161 (accept_3_2 10 18 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 18 161 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 18 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 161
  (Polychromatic418967fa.accept_15_8_3_11_1_849 8 18 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 18 161 (accept_3_2 7 18 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18
  161 (Polychromatic418967fa.accept_15_6_3_11_1_848 6 18 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 18 161 (Polychromatic418967fa.accept_19_5_18_9_1_8830 5 18 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 161 (accept_3_2 4 18 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 18 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 18 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 18 161
  (Polychromatic418967fa.accept_19_2_18_9_1_8829 2 18 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 18 161 (accept_3_2 1 18 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18
  161)))))))))))))))))) (allB_succ 17 161 (allA_succ_of_accept 16 17 161 (accept_3_2 16 17 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 161 (Polychromatic418967fa.accept_13_2_4_5_1_3152 15 17 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 161
  (Polychromatic418967fa.accept_10_4_7_1_1_471 14 17 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 161 (accept_3_2 13 17 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  17 161 (Polychromatic418967fa.accept_11_1_6_7_1_116 12 17 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 161 (Polychromatic418967fa.accept_14_11_3_7_1_604 11 17 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 161 (accept_3_2 10 17 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 161 (Polychromatic418967fa.accept_13_9_4_5_1_1651 9 17 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 161
  (Polychromatic418967fa.accept_19_8_17_9_1_4542 8 17 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 161 (accept_3_2 7 17 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  161 (Polychromatic418967fa.accept_10_6_7_1_1_1297 6 17 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 17 161 (Polychromatic418967fa.accept_15_5_2_11_1_1596 5 17 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 161 (accept_3_2 4 17 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 17 161 (Polychromatic418967fa.accept_21_3_17_14_1_8828 3 17 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 161
  (Polychromatic418967fa.accept_13_2_4_5_1_3152 2 17 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 17 161 (accept_3_2 1 17 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17
  161))))))))))))))))) (allB_succ 16 161 (allA_of_3_0 16 16 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15
  161 (allA_succ_of_accept 14 15 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 15 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 161 (accept_3_2 13 15 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 15 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 15 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 161 (Polychromatic418967fa.accept_9_2_6_8_1_321 11
  15 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 161 (accept_3_2 10 15
  161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 161
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 15 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 15 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 15 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 161 (accept_3_2 7 15 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 15 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 15 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 15 161 (Polychromatic418967fa.accept_9_5_6_8_1_101 5
  15 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 161 (accept_3_2 4 15 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 15 161 (Polychromatic418967fa.accept_9_3_6_8_1_308 3
  15 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 161
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 15 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 15 161 (accept_3_2 1 15 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15
  161))))))))))))))) (allB_succ 14 161 (allA_succ_of_accept 13 14 161 (accept_3_2 13 14 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 14 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 14 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 14 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 11
  14 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 14 161 (accept_3_2 10 14
  161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 14 161 (Polychromatic418967fa.accept_6_3_2_5_1_32
  9 14 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 14 161
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 14 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 14 161 7 1 2 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 14 161 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 14 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 14 161 (Polychromatic418967fa.accept_10_5_4_1_1_842 5 14 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 14 161 (accept_3_2 4 14 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 14 161 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 14
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 14 161
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 14 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 14 161 (accept_3_2 1 14 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14
  161)))))))))))))) (allB_succ 13 161 (allA_of_3_0 13 13 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 12 161
  (allA_succ_of_accept 11 12 161 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 12 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 161 (accept_3_2 10 12 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 12 161 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 12 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 161 (Polychromatic418967fa.accept_13_8_12_5_1_1604
  8 12 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 12 161 (accept_3_2 7 12
  161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12 161 (Polychromatic418967fa.accept_9_6_3_8_1_595
  6 12 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 12 161
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 12 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 12 161 (accept_3_2 4 12 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 12
  161 (Polychromatic418967fa.accept_10_3_2_1_1_839 3 12 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 12 161 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 12 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12 161 (accept_3_2 1 12 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 12 161)))))))))))) (allB_succ 11 161 (allA_succ_of_accept 10 11 161 (accept_3_2 10 11 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 161 (Polychromatic418967fa.accept_17_9_11_8_1_5077
  9 11 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 11 161
  (Polychromatic418967fa.accept_19_8_11_9_1_8827 8 11 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 11 161 (accept_3_2 7 11 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 11
  161 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 11 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 11 161 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 11 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 161 (accept_3_2 4 11 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 11 161 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 11 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 11
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 11 161 (accept_3_2 1 11 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11 161))))))))))) (allB_succ 10 161 (allA_of_3_0 10 10 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 9 161 (allA_succ_of_accept 8 9 161
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 9 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 9 161 (accept_3_2 7 9 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 161
  (Polychromatic418967fa.accept_15_6_9_11_1_858 6 9 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 9 161 (Polychromatic418967fa.accept_10_5_9_1_1_187 5 9 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 161 (accept_3_2 4 9 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 9 161 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 9 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 161 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 9
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 161 (accept_3_2 1 9 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 161))))))))) (allB_succ 8 161 (allA_succ_of_accept 7 8 161
  (accept_3_2 7 8 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 8 161
  (Polychromatic418967fa.accept_14_6_8_7_1_589 6 8 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 8 161 (Polychromatic418967fa.accept_15_5_8_11_1_2350 5 8 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 8 161 (accept_3_2 4 8 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 8 161 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 8 161 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 8 161 (Polychromatic418967fa.accept_12_2_8_5_1_408 2 8
  161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 8 161 (accept_3_2 1 8 161
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 161)))))))) (allB_succ 7 161 (allA_of_3_0 7 7 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 6 161 (allA_succ_of_accept 5 6 161
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 6 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 161 (accept_3_2 4 6 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 6 161
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 6 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 6 161 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 6 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 161 (accept_3_2 1 6 161 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 6 161)))))) (allB_succ 5 161 (allA_succ_of_accept 4 5 161 (accept_3_2 4 5 161 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 161 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 5 161
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 161
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 5 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 5 161 (accept_3_2 1 5 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 161)))))
  (allB_succ 4 161 (allA_of_3_0 4 4 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 3 161 (allA_succ_of_accept 2
  3 161 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 3 161 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 3 161 (accept_3_2 1 3 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 161)))
  (allB_succ 2 161 (allA_succ_of_accept 1 2 161 (accept_3_2 1 2 161 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2
  161)) (allB_two
  161)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


