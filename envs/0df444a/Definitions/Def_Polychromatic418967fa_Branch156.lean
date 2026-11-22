-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch156
-- name    : Polychromatic418967fa_Branch156
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:15:14.486681+00:00
-- url     : https://prove2.me/theorems/a3c774b3-55cd-4dfd-a46c-4c8ae26ba6d3
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch156_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_156 : allB 156 156 :=
  allB_succ' 2 155 156 (Eq.refl Bool.true) (allA_succ_of_accept 1 155 156 (accept_3_4 1 155 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 155 156)) (allB_succ' 3 154 156 (Eq.refl Bool.true) (allA_succ_of_gcd 2 154 156 2 1 77
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 154 156
  (Polychromatic418967fa.accept_36_1_10_12_1_8529 1 154 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 154 156))) (allB_succ' 4 153 156 (Eq.refl Bool.true) (allA_succ_of_gcd 3 153 156 3 1 51 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 153 156
  (Polychromatic418967fa.accept_16_2_9_12_1_46 2 153 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 153 156 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 153 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 153 156)))) (allB_succ' 5 152 156 (Eq.refl Bool.true) (allA_succ_of_gcd 4
  152 156 4 1 38 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  3 152 156 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 152 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 152 156 2 1 76 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 152 156 (accept_3_4 1 152 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152
  156))))) (allB_succ' 6 151 156 (Eq.refl Bool.true) (allA_succ_of_accept 5 151 156 (accept_3_5 5 151 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 151 156 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 151 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 151 156
  (Polychromatic418967fa.accept_8_3_7_4_1_42 3 151 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 151 156 (accept_3_5 2 151 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  151 156 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 151 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 151 156)))))) (allB_succ' 7 150 156 (Eq.refl Bool.true) (allA_succ_of_gcd 6 150 156 6 1 25 26
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 150 156
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 150 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 150 156 2 2 75 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 150 156 3 1 50 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 150 156 2 1 75 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 150 156 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 150 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 150 156))))))) (allB_succ' 8 149 156 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 149 156 (accept_3_4 7 149 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  149 156 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 149 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 149 156 (Polychromatic418967fa.accept_10_5_9_6_1_697 5 149 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 149 156 (accept_3_4 4 149 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 149 156 (Polychromatic418967fa.accept_10_3_9_6_1_94 3 149 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 149 156
  (Polychromatic418967fa.accept_9_2_5_3_1_37 2 149 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 149 156 (accept_3_4 1 149 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 149
  156)))))))) (allB_succ' 9 148 156 (Eq.refl Bool.true) (allA_succ_of_gcd 8 148 156 4 2 37 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 148 156
  (Polychromatic418967fa.accept_9_7_4_3_1_204 7 148 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 148 156 2 3 74 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 148 156 (accept_3_5 5 148 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 148
  156 4 1 37 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  148 156 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 148 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 148 156 2 1 74 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 148 156 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 148 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 148 156))))))))) (allB_succ' 10 147 156 (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 147 156 3 3 49 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 147 156 (Polychromatic418967fa.accept_16_8_3_12_1_1819 8 147 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 156 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 147 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 147 156 3 2 49 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 147 156
  (Polychromatic418967fa.accept_14_5_7_2_1_468 5 147 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 147 156 (Polychromatic418967fa.accept_16_4_3_12_1_4892 4 147 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 147 156 3 1 49 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 147 156 (Polychromatic418967fa.accept_15_2_12_6_1_3063 2 147 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 156
  (Polychromatic418967fa.accept_10_1_7_6_1_91 1 147 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 147 156)))))))))) (allB_succ' 11 146 156 (Eq.refl Bool.true) (allA_succ_of_gcd 10 146 156 2 5 73 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 146 156
  (Polychromatic418967fa.accept_15_9_11_6_1_637 9 146 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 146 156 2 4 73 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 146 156 (accept_3_4 7 146 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 146
  156 2 3 73 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  146 156 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 146 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 146 156 2 2 73 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 146 156 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 146 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 146 156 2 1 73 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 146 156 (accept_3_4 1 146 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 146 156))))))))))) (allB_succ' 12 145 156 (Eq.refl Bool.true) (allA_succ_of_accept 11
  145 156 (accept_3_5 11 145 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 145 156
  (Polychromatic418967fa.accept_7_3_5_2_1_17 10 145 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 145 156 (Polychromatic418967fa.accept_10_9_5_6_1_691 9 145 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 145 156 (accept_3_5 8 145 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 145 156 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 145 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 145 156 (Polychromatic418967fa.accept_9_6_1_3_1_191 6
  145 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 145 156 (accept_3_5 5 145
  156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 145 156
  (Polychromatic418967fa.accept_7_4_5_2_1_243 4 145 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 145 156 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 145 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 145 156 (accept_3_5 2 145 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 145 156 (Polychromatic418967fa.accept_10_1_5_6_1_649 1 145 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 145 156)))))))))))) (allB_succ' 13 144 156 (Eq.refl Bool.true)
  (allA_succ_of_gcd 12 144 156 12 1 12 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 144 156 (Polychromatic418967fa.accept_15_11_9_6_1_1321 11 144 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 144 156 2 5 72 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 144 156 3 3 48 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 144 156 4 2 36 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 144 156
  (Polychromatic418967fa.accept_19_7_11_4_1_1872 7 144 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 144 156 6 1 24 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 144 156 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 144 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 144 156 4 1 36 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 144 156 3 1 48 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 144 156 2 1 72 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 144 156 (Polychromatic418967fa.accept_15_1_9_6_1_1323 1 144 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144 156))))))))))))) (allB_succ' 14 143 156
  (Eq.refl Bool.true) (allA_succ_of_gcd 13 143 156 13 1 11 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12 143 156 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 143 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 143 156
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 143 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 143 156 (accept_3_4 10 143 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  143 156 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 143 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 143 156 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 143 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 143 156 (accept_3_4 7 143 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 143 156 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 143 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 143 156
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 143 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 143 156 (accept_3_4 4 143 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  143 156 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 143 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 143 156 (Polychromatic418967fa.accept_9_2_8_3_1_181 2 143 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 143 156 (accept_3_4 1 143 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 143 156)))))))))))))) (allB_succ' 15 142 156 (Eq.refl Bool.true) (allA_succ_of_gcd 14
  142 156 2 7 71 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  13 142 156 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 142 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 142 156 2 6 71 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 142 156 (accept_3_5 11 142 156 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 142 156 2 5 71 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 142 156 (Polychromatic418967fa.accept_17_9_6_3_1_2398 9 142 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 142 156 2 4 71 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 142 156 (Polychromatic418967fa.accept_21_7_16_9_1_2417 7 142 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 142 156 2 3 71 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 142 156 (accept_3_5 5 142 156
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 142 156 2 2 71 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 142 156 (Polychromatic418967fa.accept_21_3_16_9_1_8528
  3 142 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 142 156 2 1 71 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 142 156
  (Polychromatic418967fa.accept_9_1_7_3_1_41 1 142 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 142 156))))))))))))))) (allB_succ' 16 141 156 (Eq.refl Bool.true) (allA_succ_of_gcd 15 141 156 3 5 47 52
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 141 156
  (Polychromatic418967fa.accept_9_5_6_3_1_40 14 141 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 141 156 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 141 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 141 156 3 4 47 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 141 156 (Polychromatic418967fa.accept_9_2_6_3_1_178 11
  141 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 141 156
  (Polychromatic418967fa.accept_7_3_1_2_1_247 10 141 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 141 156 3 3 47 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 141 156 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 141 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 156 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 141 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 141 156 3 2 47 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 141 156
  (Polychromatic418967fa.accept_9_5_6_3_1_40 5 141 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 141 156 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 141 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 141 156 3 1 47 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 141 156 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 141 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 156
  (Polychromatic418967fa.accept_8_1_5_4_1_388 1 141 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 141 156)))))))))))))))) (allB_succ' 17 140 156 (Eq.refl Bool.true) (allA_succ_of_gcd 16 140 156 4 4 35 39
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 140 156
  (Polychromatic418967fa.accept_9_6_5_3_1_205 15 140 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 140 156 2 7 70 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 140 156 (accept_3_4 13 140 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12
  140 156 4 3 35 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  11 140 156 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 140 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 140 156 2 5 70 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 140 156 (Polychromatic418967fa.accept_25_9_15_6_1_8527 9 140 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 140 156 4 2 35 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 140 156 (accept_3_4 7 140 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 140 156 2 3 70 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 140 156 (Polychromatic418967fa.accept_11_5_8_2_1_588 5 140 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 140 156 4 1 35 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 140 156
  (Polychromatic418967fa.accept_15_3_5_6_1_4005 3 140 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 140 156 2 1 70 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 140 156 (accept_3_4 1 140 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140
  156))))))))))))))))) (allB_succ' 18 139 156 (Eq.refl Bool.true) (allA_succ_of_accept 17 139 156 (accept_3_5 17 139 156
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 139 156 (Polychromatic418967fa.accept_9_7_4_3_1_204
  16 139 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 139 156
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 139 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 139 156 (accept_3_5 14 139 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 139 156 (Polychromatic418967fa.accept_10_3_9_6_1_94 13 139 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 139 156 (Polychromatic418967fa.accept_19_12_6_4_1_2992 12 139 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 139 156 (accept_3_5 11 139 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 139 156 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 139 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 139 156
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 139 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 139 156 (accept_3_5 8 139 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  139 156 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 139 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 139 156 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 139 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 139 156 (accept_3_5 5 139 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 139 156 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 139 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 139 156
  (Polychromatic418967fa.accept_7_3_6_2_1_90 3 139 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 139 156 (accept_3_5 2 139 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  139 156 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 139 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 139 156)))))))))))))))))) (allB_succ' 19 138 156 (Eq.refl Bool.true) (allA_succ_of_gcd 18 138
  156 6 3 23 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  138 156 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 138 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 138 156 2 8 69 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 15 138 156 3 5 46 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 14 138 156 2 7 69 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 138 156 (Polychromatic418967fa.accept_10_3_8_6_1_326 13 138 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 138 156 6 2 23 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 138 156
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 138 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 138 156 2 5 69 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 138 156 3 3 46 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 138 156 2 4 69 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 138 156 (Polychromatic418967fa.accept_14_7_12_2_1_2502 7 138 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 138 156 6 1 23 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 138 156 (Polychromatic418967fa.accept_15_5_3_6_1_2128 5 138 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 138 156 2 2 69 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 138 156 3 1 46 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 138 156 2 1 69 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 138 156
  (Polychromatic418967fa.accept_15_1_3_6_1_621 1 138 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 138 156))))))))))))))))))) (allB_succ' 20 137 156 (Eq.refl Bool.true) (allA_succ_of_accept 19 137 156
  (accept_3_4 19 137 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 137 156
  (Polychromatic418967fa.accept_16_2_9_12_1_46 18 137 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 137 156 (Polychromatic418967fa.accept_9_8_2_3_1_447 17 137 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 137 156 (accept_3_4 16 137 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 137 156 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 137 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 137 156 (Polychromatic418967fa.accept_9_5_2_3_1_194
  14 137 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 137 156 (accept_3_4 13
  137 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 137 156
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 137 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 137 156 (Polychromatic418967fa.accept_10_1_7_6_1_91 11 137 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 137 156 (accept_3_4 10 137 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 137 156 (Polychromatic418967fa.accept_14_9_11_2_1_2501 9 137 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 156
  (Polychromatic418967fa.accept_9_8_2_3_1_447 8 137 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 137 156 (accept_3_4 7 137 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  137 156 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 137 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 137 156 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 137 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 156 (accept_3_4 4 137 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 137 156 (Polychromatic418967fa.accept_10_3_7_6_1_659 3 137 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 137 156
  (Polychromatic418967fa.accept_16_2_9_12_1_46 2 137 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 137 156 (accept_3_4 1 137 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 137
  156)))))))))))))))))))) (allB_succ' 21 136 156 (Eq.refl Bool.true) (allA_succ_of_gcd 20 136 156 4 5 34 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 136 156
  (Polychromatic418967fa.accept_7_5_3_2_1_249 19 136 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 136 156 2 9 68 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 136 156 (accept_3_5 17 136 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  136 156 4 4 34 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 136 156 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 136 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 136 156 2 7 68 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 136 156 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 136 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 136 156 4 3 34 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 136 156 (accept_3_5 11 136 156
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 136 156 2 5 68 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 136 156
  (Polychromatic418967fa.accept_11_9_4_2_1_600 9 136 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 136 156 4 2 34 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 136 156 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 136 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 136 156 2 3 68 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 136 156 (accept_3_5 5 136 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 136 156 4 1 34 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 136 156 (Polychromatic418967fa.accept_15_3_1_6_1_206 3 136 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 136 156 2 1 68 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 136 156 (Polychromatic418967fa.accept_7_1_3_2_1_13 1
  136 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 136 156)))))))))))))))))))))
  (allB_succ' 22 135 156 (Eq.refl Bool.true) (allA_succ_of_gcd 21 135 156 3 7 45 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 135 156
  (Polychromatic418967fa.accept_16_4_7_12_1_2734 20 135 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 135 156 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 135 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 135 156 3 6 45 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 135 156
  (Polychromatic418967fa.accept_18_17_9_12_1_2160 17 135 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 135 156 (Polychromatic418967fa.accept_18_16_9_12_1_1182 16 135 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 135 156 3 5 45 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 135 156
  (Polychromatic418967fa.accept_10_4_5_6_1_651 14 135 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 135 156 (Polychromatic418967fa.accept_17_13_16_3_1_1431 13 135 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 135 156 3 4 45 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 135 156
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 135 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 135 156 (Polychromatic418967fa.accept_18_10_9_12_1_3259 10 135 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 135 156 3 3 45 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 135 156 (Polychromatic418967fa.accept_16_8_7_12_1_7207
  8 135 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 156
  (Polychromatic418967fa.accept_14_7_9_2_1_2489 7 135 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 135 156 3 2 45 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 135 156 (Polychromatic418967fa.accept_16_5_7_12_1_7206 5 135 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 135 156 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 135 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 135 156 3 1 45 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 135 156
  (Polychromatic418967fa.accept_16_2_7_12_1_3793 2 135 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 135 156 (Polychromatic418967fa.accept_10_1_5_6_1_649 1 135 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 135 156)))))))))))))))))))))) (allB_succ' 23 134 156 (Eq.refl Bool.true)
  (allA_succ_of_gcd 22 134 156 2 11 67 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 134 156 (Polychromatic418967fa.accept_18_3_8_12_1_3283 21 134 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 134 156 2 10 67 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 134 156 (accept_3_4 19 134 156
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 134 156 2 9 67 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 134 156
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 134 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 134 156 2 8 67 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 134 156 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 134 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 134 156 2 7 67 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 134 156 (accept_3_4 13 134 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 134 156 2 6 67 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 134 156 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 134 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 134 156 2 5 67 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 134 156
  (Polychromatic418967fa.accept_15_9_14_6_1_3004 9 134 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 134 156 2 4 67 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 134 156 (accept_3_4 7 134 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 134
  156 2 3 67 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  134 156 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 134 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 134 156 2 2 67 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 134 156 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 134 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 134 156 2 1 67 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 134 156 (accept_3_4 1 134 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 134 156))))))))))))))))))))))) (allB_succ' 24 133 156 (Eq.refl Bool.true)
  (allA_succ_of_accept 23 133 156 (accept_3_5 23 133 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 133 156 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 133 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 133 156 (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 133 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 133 156 (accept_3_5 20 133 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 133 156 (Polychromatic418967fa.accept_9_1_7_3_1_41 19 133 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 133 156
  (Polychromatic418967fa.accept_10_8_3_6_1_685 18 133 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 133 156 (accept_3_5 17 133 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 133 156 (Polychromatic418967fa.accept_21_16_7_9_1_6877 16 133 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 133 156 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 133 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 133 156 (accept_3_5 14 133 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 133 156 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 133 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 133 156
  (Polychromatic418967fa.accept_14_12_7_2_1_1663 12 133 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 133 156 (accept_3_5 11 133 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 133 156 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 133 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 133 156 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 133 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 133 156 (accept_3_5 8 133 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 133 156 (Polychromatic418967fa.accept_10_7_3_6_1_644 7 133 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 133 156
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 133 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 133 156 (accept_3_5 5 133 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  133 156 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 133 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 133 156 (Polychromatic418967fa.accept_11_3_1_2_1_1063 3 133 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 133 156 (accept_3_5 2 133 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 133 156 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 133 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 133 156)))))))))))))))))))))))) (allB_succ' 25 132 156
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 132 156 12 2 11 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 132 156 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 132 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 132 156 2 11 66 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 132 156 3 7 44 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 132 156 4 5 33 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 132 156
  (Polychromatic418967fa.accept_9_1_6_3_1_177 19 132 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 132 156 6 3 22 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 132 156 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 132 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 132 156 4 4 33 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 132 156 3 5 44 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 132 156 2 7 66 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 132 156 (Polychromatic418967fa.accept_9_4_6_3_1_179 13
  132 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 132 156 12 1 11 13 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 132 156
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 132 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 132 156 2 5 66 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 132 156 3 3 44 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 132 156 4 2 33 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 132 156 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 132 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132 156 6 1 22 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 132 156 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 132 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 132 156 4 1 33 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 132 156 3 1 44 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 132 156 2 1 66 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 132 156
  (Polychromatic418967fa.accept_7_1_6_2_1_18 1 132 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 132 156))))))))))))))))))))))))) (allB_succ' 26 131 156 (Eq.refl Bool.true) (allA_succ_of_accept 25 131 156
  (accept_3_4 25 131 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 131 156
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 131 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 131 156 (Polychromatic418967fa.accept_8_7_3_4_1_404 23 131 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 131 156 (accept_3_4 22 131 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 131 156 (Polychromatic418967fa.accept_14_7_5_2_1_2473 21 131 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 131 156
  (Polychromatic418967fa.accept_9_2_5_3_1_37 20 131 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 131 156 (accept_3_4 19 131 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 131 156 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 131 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 131 156 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 131 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 131 156 (accept_3_4 16 131 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 131 156 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 131 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 131 156
  (Polychromatic418967fa.accept_21_14_5_9_1_8526 14 131 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 131 156 (accept_3_4 13 131 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 131 156 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 131 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 131 156 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 131 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 131 156 (accept_3_4 10 131 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 131 156 (Polychromatic418967fa.accept_15_9_11_6_1_637 9 131 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 131 156
  (Polychromatic418967fa.accept_9_8_5_3_1_777 8 131 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 131 156 (accept_3_4 7 131 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  131 156 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 131 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 131 156 (Polychromatic418967fa.accept_10_5_1_6_1_672 5 131 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 131 156 (accept_3_4 4 131 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 131 156 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 131 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 131 156
  (Polychromatic418967fa.accept_9_2_5_3_1_37 2 131 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 131 156 (accept_3_4 1 131 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 131
  156)))))))))))))))))))))))))) (allB_succ' 27 130 156 (Eq.refl Bool.true) (allA_succ_of_gcd 26 130 156 26 1 5 6
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 130 156
  (Polychromatic418967fa.accept_9_7_4_3_1_204 25 130 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 130 156 2 12 65 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 130 156 (accept_3_5 23 130 156 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 130 156 2 11 65 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 130 156 (Polychromatic418967fa.accept_19_2_16_4_1_8525 21 130 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 130 156 2 10 65 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 130 156
  (Polychromatic418967fa.accept_7_5_4_2_1_235 19 130 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 130 156 2 9 65 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 130 156 (accept_3_5 17 130 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  130 156 2 8 65 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 130 156 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 130 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 130 156 2 7 65 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 13 130 156 13 1 10 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 12 130 156 2 6 65 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 130 156 (accept_3_5 11 130 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 130 156 2 5 65 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 130 156 (Polychromatic418967fa.accept_14_9_4_2_1_983 9 130 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 130 156 2 4 65 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 130 156
  (Polychromatic418967fa.accept_9_7_4_3_1_204 7 130 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 130 156 2 3 65 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 130 156 (accept_3_5 5 130 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 130
  156 2 2 65 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  130 156 (Polychromatic418967fa.accept_15_3_10_6_1_632 3 130 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 130 156 2 1 65 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 130 156 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 130 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 130 156))))))))))))))))))))))))))) (allB_succ' 28 129 156 (Eq.refl
  Bool.true) (allA_succ_of_gcd 27 129 156 3 9 43 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 26 129 156 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 129 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 156 (Polychromatic418967fa.accept_10_5_9_6_1_697
  25 129 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 129 156 3 8 43 52
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 129 156
  (Polychromatic418967fa.accept_10_3_9_6_1_94 23 129 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 129 156 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 129 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 129 156 3 7 43 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 129 156 (Polychromatic418967fa.accept_7_6_3_2_1_461 20
  129 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 156
  (Polychromatic418967fa.accept_7_5_3_2_1_249 19 129 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 129 156 3 6 43 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 129 156 (Polychromatic418967fa.accept_21_17_3_9_1_8524 17 129 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 156 (Polychromatic418967fa.accept_11_5_8_2_1_588 16 129
  156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 129 156 3 5 43 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 129 156
  (Polychromatic418967fa.accept_15_14_9_6_1_5093 14 129 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 129 156 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 129 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 129 156 3 4 43 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 129 156 (Polychromatic418967fa.accept_15_11_9_6_1_1321
  11 129 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 156
  (Polychromatic418967fa.accept_19_10_15_4_1_1852 10 129 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 9 129 156 3 3 43 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 129 156 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 129 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 156 (Polychromatic418967fa.accept_17_7_10_3_1_1421
  7 129 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 129 156 3 2 43 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 129 156
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 129 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 129 156 (Polychromatic418967fa.accept_15_4_9_6_1_627 4 129 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 129 156 3 1 43 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 129 156 (Polychromatic418967fa.accept_16_2_1_12_1_3798 2 129 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 156
  (Polychromatic418967fa.accept_7_1_3_2_1_13 1 129 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 129 156)))))))))))))))))))))))))))) (allB_succ' 29 128 156 (Eq.refl Bool.true) (allA_succ_of_gcd 28 128 156
  4 7 32 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 128
  156 (Polychromatic418967fa.accept_17_10_9_3_1_7144 27 128 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 128 156 2 13 64 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 128 156 (accept_3_4 25 128 156 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 128 156 4 6 32 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 128 156 (Polychromatic418967fa.accept_9_5_2_3_1_194 23 128 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 128 156 2 11 64 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 128 156 (Polychromatic418967fa.accept_18_3_2_12_1_5751
  21 128 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 128 156 4 5 32 39
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 128 156
  (accept_3_4 19 128 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 128 156 2 9 64 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 128 156
  (Polychromatic418967fa.accept_9_8_2_3_1_447 17 128 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 128 156 4 4 32 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 128 156 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 128 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 128 156 2 7 64 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 128 156 (accept_3_4 13 128 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 128 156 4 3 32 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 128 156 (Polychromatic418967fa.accept_17_11_9_3_1_1463 11 128
  156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 128 156 2 5 64 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 128 156
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 128 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 128 156 4 2 32 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 128 156 (accept_3_4 7 128 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 128
  156 2 3 64 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  128 156 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 128 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 128 156 4 1 32 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 128 156 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 128 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 128 156 2 1 64 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 128 156 (accept_3_4 1 128 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 128 156))))))))))))))))))))))))))))) (allB_succ' 30 127 156 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 127 156 (accept_3_5 29 127 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 127 156 (Polychromatic418967fa.accept_15_13_7_6_1_682 28 127 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 127 156 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 127 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 127 156 (accept_3_5 26 127 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 127 156 (Polychromatic418967fa.accept_9_7_1_3_1_443 25 127 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 127 156
  (Polychromatic418967fa.accept_7_3_1_2_1_247 24 127 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 127 156 (accept_3_5 23 127 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 127 156 (Polychromatic418967fa.accept_9_4_1_3_1_190 22 127 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 127 156 (Polychromatic418967fa.accept_10_1_7_6_1_91 21 127 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 127 156 (accept_3_5 20 127 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 127 156 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 127 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 127 156
  (Polychromatic418967fa.accept_16_2_15_12_1_1744 18 127 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 127 156 (accept_3_5 17 127 156 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 127 156 (Polychromatic418967fa.accept_9_7_1_3_1_443 16 127 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 127 156 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 127 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 127 156 (accept_3_5 14 127 156
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 127 156 (Polychromatic418967fa.accept_7_6_1_2_1_230
  13 127 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 127 156
  (Polychromatic418967fa.accept_15_12_7_6_1_4013 12 127 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 127 156 (accept_3_5 11 127 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 127 156 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 127 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 127 156 (Polychromatic418967fa.accept_19_9_13_4_1_2982 9 127 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 127 156 (accept_3_5 8 127 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 127 156 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 127 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 127 156
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 127 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 127 156 (accept_3_5 5 127 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  127 156 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 127 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 127 156 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 127 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 127 156 (accept_3_5 2 127 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 127 156 (Polychromatic418967fa.accept_10_1_7_6_1_91 1 127 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 127 156)))))))))))))))))))))))))))))) (allB_succ' 31 126
  156 (Eq.refl Bool.true) (allA_succ_of_gcd 30 126 156 6 5 21 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 126 156 (Polychromatic418967fa.accept_17_12_7_3_1_1498 29 126
  156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 126 156 2 14 63 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 126 156 3 9 42 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 126 156 2 13 63 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 126 156
  (Polychromatic418967fa.accept_19_6_12_4_1_8516 25 126 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 126 156 6 4 21 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 126 156 (Polychromatic418967fa.accept_24_23_6_12_1_8453 23 126 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 126 156 2 11 63 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 126 156 3 7 42 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 126 156 2 10 63 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 126 156
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 19 126 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 126 156 6 3 21 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 126 156 (Polychromatic418967fa.accept_20_17_6_16_1_8482 17 126 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 126 156 2 8 63 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 126 156 3 5 42 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 126 156 2 7 63 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 126 156
  (Polychromatic418967fa.accept_22_13_16_2_1_8523 13 126 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 126 156 6 2 21 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 126 156 (Polychromatic418967fa.accept_19_11_12_4_1_8455 11 126 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 126 156 2 5 63 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 126 156 3 3 42 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 126 156 2 4 63 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 126 156
  (Polychromatic418967fa.accept_19_7_12_4_1_8522 7 126 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 126 156 6 1 21 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 126 156 (Polychromatic418967fa.accept_19_5_12_4_1_8467 5 126 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 126 156 2 2 63 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 126 156 3 1 42 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 126 156 2 1 63 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 126 156 (Polychromatic418967fa.accept_19_1_12_4_1_4263 1 126 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126 156)))))))))))))))))))))))))))))))
  (allB_succ' 32 125 156 (Eq.refl Bool.true) (allA_succ_of_accept 31 125 156 (accept_3_4 31 125 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 125 156 (Polychromatic418967fa.accept_20_10_5_16_1_7004 30 125 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 125 156
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 125 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 125 156 (accept_3_4 28 125 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 125 156 (Polychromatic418967fa.accept_15_12_5_6_1_2148 27 125 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 125 156 (Polychromatic418967fa.accept_15_11_5_6_1_669 26 125 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 125 156 (accept_3_4 25 125 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 125 156 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 125 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 125 156
  (Polychromatic418967fa.accept_9_5_8_3_1_437 23 125 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 125 156 (accept_3_4 22 125 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 125 156 (Polychromatic418967fa.accept_10_1_5_6_1_649 21 125 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 125 156 (Polychromatic418967fa.accept_9_2_8_3_1_181 20 125 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 125 156 (accept_3_4 19 125 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 125 156 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 125 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 125 156
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 125 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 125 156 (accept_3_4 16 125 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 125 156 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 125 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 125 156 (Polychromatic418967fa.accept_9_5_8_3_1_437 14 125 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 125 156 (accept_3_4 13 125 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 125 156 (Polychromatic418967fa.accept_15_12_5_6_1_2148 12 125 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 125 156
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 125 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 125 156 (accept_3_4 10 125 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  125 156 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 125 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 125 156 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 125 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 125 156 (accept_3_4 7 125 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 125 156 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 125 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 125 156
  (Polychromatic418967fa.accept_9_5_8_3_1_437 5 125 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 125 156 (accept_3_4 4 125 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  125 156 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 125 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 125 156 (Polychromatic418967fa.accept_9_2_8_3_1_181 2 125 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 125 156 (accept_3_4 1 125 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 125 156)))))))))))))))))))))))))))))))) (allB_succ' 33 124 156 (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 124 156 4 8 31 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 124 156 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 124 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 124 156 2 15 62 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 124 156 (accept_3_5 29 124 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 124 156 4 7 31 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 124 156 (Polychromatic418967fa.accept_18_9_16_12_1_1143 27 124
  156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 124 156 2 13 62 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 124 156
  (Polychromatic418967fa.accept_7_4_5_2_1_243 25 124 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 124 156 4 6 31 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 124 156 (accept_3_5 23 124 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  124 156 2 11 62 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 124 156 (Polychromatic418967fa.accept_14_7_12_2_1_2502 21 124 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 124 156 4 5 31 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 124 156 (Polychromatic418967fa.accept_9_1_7_3_1_41 19
  124 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 124 156 2 9 62 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 124 156 (accept_3_5 17
  124 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 124 156 4 4 31 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 124 156
  (Polychromatic418967fa.accept_9_6_7_3_1_436 15 124 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 124 156 2 7 62 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 124 156 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 124 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 124 156 4 3 31 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 124 156 (accept_3_5 11 124 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 124 156 2 5 62 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 124 156 (Polychromatic418967fa.accept_15_9_4_6_1_3075 9 124 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 124 156 4 2 31 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 124 156
  (Polychromatic418967fa.accept_14_7_12_2_1_2502 7 124 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 124 156 2 3 62 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 124 156 (accept_3_5 5 124 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 124
  156 4 1 31 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  124 156 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 124 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 124 156 2 1 62 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 124 156 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 124 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 124 156))))))))))))))))))))))))))))))))) (allB_succ' 34 123 156
  (Eq.refl Bool.true) (allA_succ_of_gcd 33 123 156 3 11 41 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 123 156 (Polychromatic418967fa.accept_9_5_6_3_1_40 32 123 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 156
  (Polychromatic418967fa.accept_8_7_3_4_1_404 31 123 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 123 156 3 10 41 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 123 156 (Polychromatic418967fa.accept_9_2_6_3_1_178 29 123 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 123 156 (Polychromatic418967fa.accept_9_1_6_3_1_177
  28 123 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 123 156 3 9 41 52
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 123 156
  (Polychromatic418967fa.accept_7_5_4_2_1_235 26 123 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 123 156 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 123 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 123 156 3 8 41 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 123 156 (Polychromatic418967fa.accept_8_7_3_4_1_404 23
  123 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 123 156
  (Polychromatic418967fa.accept_9_4_6_3_1_179 22 123 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 123 156 3 7 41 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 123 156 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 123 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 156 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 123 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 123 156 3 6 41 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 123 156
  (Polychromatic418967fa.accept_9_8_6_3_1_457 17 123 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 123 156 (Polychromatic418967fa.accept_9_7_6_3_1_456 16 123 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 123 156 3 5 41 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 123 156 (Polychromatic418967fa.accept_9_5_6_3_1_40 14
  123 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 156
  (Polychromatic418967fa.accept_7_6_4_2_1_236 13 123 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 123 156 3 4 41 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 123 156 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 123 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 123 156 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 123 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 123 156 3 3 41 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 123 156
  (Polychromatic418967fa.accept_9_8_6_3_1_457 8 123 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 123 156 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 123 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 123 156 3 2 41 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 123 156 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 123 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 156
  (Polychromatic418967fa.accept_9_4_6_3_1_179 4 123 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 123 156 3 1 41 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 123 156 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 123 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 156 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 123 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 123 156))))))))))))))))))))))))))))))))))
  (allB_succ' 35 122 156 (Eq.refl Bool.true) (allA_succ_of_gcd 34 122 156 2 17 61 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 122 156
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 122 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 122 156 2 16 61 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 122 156 (accept_3_4 31 122 156 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 122 156 2 15 61 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 122 156 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 122 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 122 156 2 14 61 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 122 156
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 122 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 122 156 2 13 61 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 122 156 (accept_3_4 25 122 156 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 122 156 2 12 61 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 122 156 (Polychromatic418967fa.accept_15_8_2_6_1_2125 23 122 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 122 156 2 11 61 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 122 156
  (Polychromatic418967fa.accept_10_1_2_6_1_638 21 122 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 122 156 2 10 61 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 122 156 (accept_3_4 19 122 156 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 122 156 2 9 61 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 122 156 (Polychromatic418967fa.accept_9_8_5_3_1_777 17 122 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 122 156 2 8 61 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 122 156 (Polychromatic418967fa.accept_7_1_3_2_1_13 15
  122 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 122 156 2 7 61 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 122 156 (accept_3_4 13
  122 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 122 156 2 6 61 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 122 156
  (Polychromatic418967fa.accept_9_2_5_3_1_37 11 122 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 122 156 2 5 61 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 122 156 (Polychromatic418967fa.accept_19_9_8_4_1_7046 9 122 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 122 156 2 4 61 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 122 156 (accept_3_4 7 122 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 122 156 2 3 61 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 122 156 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 122 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 122 156 2 2 61 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 122 156 (Polychromatic418967fa.accept_11_3_1_2_1_1063 3
  122 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 122 156 2 1 61 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 122 156 (accept_3_4 1
  122 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122 156))))))))))))))))))))))))))))))))))) (allB_succ' 36
  121 156 (Eq.refl Bool.true) (allA_succ_of_accept 35 121 156 (accept_3_5 35 121 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 121 156 (Polychromatic418967fa.accept_9_7_4_3_1_204 34 121 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 121 156 (Polychromatic418967fa.accept_9_6_4_3_1_203
  33 121 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 121 156 (accept_3_5 32
  121 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 121 156
  (Polychromatic418967fa.accept_17_14_2_3_1_7172 31 121 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 121 156 (Polychromatic418967fa.accept_19_11_7_4_1_4308 30 121 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 121 156 (accept_3_5 29 121 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 121 156 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 121 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 121 156 (Polychromatic418967fa.accept_10_7_1_6_1_673
  27 121 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 121 156 (accept_3_5 26
  121 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 121 156
  (Polychromatic418967fa.accept_9_7_4_3_1_204 25 121 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 121 156 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 121 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 121 156 (accept_3_5 23 121 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 121 156 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 121 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 121 156
  (Polychromatic418967fa.accept_8_5_1_4_1_628 21 121 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 121 156 (accept_3_5 20 121 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 121 156 (Polychromatic418967fa.accept_9_1_4_3_1_201 19 121 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 121 156 (Polychromatic418967fa.accept_14_4_9_2_1_95 18 121 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 121 156 (accept_3_5 17 121 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 121 156 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 121 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 121 156
  (Polychromatic418967fa.accept_9_6_4_3_1_203 15 121 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 121 156 (accept_3_5 14 121 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 121 156 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 121 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 121 156 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 121 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 121 156 (accept_3_5 11 121 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 121 156 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 121 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 121 156
  (Polychromatic418967fa.accept_15_9_1_6_1_657 9 121 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 121 156 (accept_3_5 8 121 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  121 156 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 121 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 121 156 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 121 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 121 156 (accept_3_5 5 121 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 121 156 (Polychromatic418967fa.accept_14_4_9_2_1_95 4 121 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 121 156
  (Polychromatic418967fa.accept_15_3_1_6_1_206 3 121 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 121 156 (accept_3_5 2 121 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  121 156 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 121 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 121 156)))))))))))))))))))))))))))))))))))) (allB_succ' 37 120 156 (Eq.refl Bool.true)
  (allA_succ_of_gcd 36 120 156 12 3 10 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 120 156 (Polychromatic418967fa.accept_16_3_8_12_1_2736 35 120 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 120 156 2 17 60 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 120 156 3 11 40 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 120 156 4 8 30 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 120 156
  (Polychromatic418967fa.accept_7_3_1_2_1_247 31 120 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 120 156 6 5 20 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 120 156 (Polychromatic418967fa.accept_14_1_8_2_1_1675 29 120 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 120 156 4 7 30 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 120 156 3 9 40 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 120 156 2 13 60 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 120 156
  (Polychromatic418967fa.accept_16_9_8_12_1_979 25 120 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 120 156 12 2 10 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 120 156 (Polychromatic418967fa.accept_11_1_10_2_1_58 23 120 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 120 156 2 11 60 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 120 156 3 7 40 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 120 156 4 5 30 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 120 156
  (Polychromatic418967fa.accept_16_3_8_12_1_2736 19 120 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 120 156 6 3 20 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 120 156 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 120 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 120 156 4 4 30 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 120 156 3 5 40 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 120 156 2 7 60 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 120 156 (Polychromatic418967fa.accept_7_6_1_2_1_230 13
  120 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 156 12 1 10 13 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 156
  (Polychromatic418967fa.accept_16_11_8_12_1_1767 11 120 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 120 156 2 5 60 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 9 120 156 3 3 40 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 8 120 156 4 2 30 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 7 120 156 (Polychromatic418967fa.accept_16_7_8_12_1_4902 7 120 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120 156 6 1 20 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 120 156
  (Polychromatic418967fa.accept_16_5_8_12_1_1766 5 120 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 120 156 4 1 30 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 120 156 3 1 40 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 120 156 2 1 60 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 120 156 (Polychromatic418967fa.accept_11_1_10_2_1_58 1 120 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 120 156))))))))))))))))))))))))))))))))))))) (allB_succ' 38 119 156 (Eq.refl
  Bool.true) (allA_succ_of_accept 37 119 156 (accept_3_4 37 119 156 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 119 156 (Polychromatic418967fa.accept_16_4_7_12_1_2734 36 119 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 119 156 (Polychromatic418967fa.accept_8_3_7_4_1_42 35 119 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 119 156 (accept_3_4 34 119 156
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 119 156 (Polychromatic418967fa.accept_9_6_2_3_1_771
  33 119 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 119 156
  (Polychromatic418967fa.accept_9_5_2_3_1_194 32 119 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 119 156 (accept_3_4 31 119 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 119 156 (Polychromatic418967fa.accept_20_10_19_16_1_8521 30 119 156 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 29 119 156 (Polychromatic418967fa.accept_11_7_9_2_1_260 29 119 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 119 156 (accept_3_4 28 119 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 119 156 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 119 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 119 156
  (Polychromatic418967fa.accept_9_8_2_3_1_447 26 119 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 119 156 (accept_3_4 25 119 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 119 156 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 119 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 119 156 (Polychromatic418967fa.accept_9_5_2_3_1_194 23 119 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 119 156 (accept_3_4 22 119 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 119 156 (Polychromatic418967fa.accept_16_5_7_12_1_7206 21 119 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 119 156
  (Polychromatic418967fa.accept_15_5_14_6_1_5120 20 119 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 119 156 (accept_3_4 19 119 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 119 156 (Polychromatic418967fa.accept_11_7_9_2_1_260 18 119 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 119 156 (Polychromatic418967fa.accept_9_8_2_3_1_447 17 119 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 119 156 (accept_3_4 16 119 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 119 156 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 119 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 119 156
  (Polychromatic418967fa.accept_9_5_2_3_1_194 14 119 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 119 156 (accept_3_4 13 119 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 119 156 (Polychromatic418967fa.accept_14_12_7_2_1_1663 12 119 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 119 156 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 119 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 156 (accept_3_4 10 119 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 119 156 (Polychromatic418967fa.accept_14_9_7_2_1_2483 9 119 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 156
  (Polychromatic418967fa.accept_9_8_2_3_1_447 8 119 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 119 156 (accept_3_4 7 119 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  119 156 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 119 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 119 156 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 119 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 156 (accept_3_4 4 119 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 119 156 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 119 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 156
  (Polychromatic418967fa.accept_16_2_7_12_1_3793 2 119 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 119 156 (accept_3_4 1 119 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  156)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 118 156 (Eq.refl Bool.true) (allA_succ_of_gcd 38 118 156 2 19
  59 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 118 156
  (Polychromatic418967fa.accept_15_7_13_6_1_696 37 118 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 118 156 2 18 59 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 118 156 (accept_3_5 35 118 156 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 118 156 2 17 59 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 118 156 (Polychromatic418967fa.accept_9_6_1_3_1_191 33 118 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 118 156 2 16 59 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 118 156
  (Polychromatic418967fa.accept_7_3_6_2_1_90 31 118 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 118 156 2 15 59 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 118 156 (accept_3_5 29 118 156 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 118 156 2 14 59 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 118 156 (Polychromatic418967fa.accept_11_5_8_2_1_588 27 118 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 118 156 2 13 59 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 118 156
  (Polychromatic418967fa.accept_7_4_6_2_1_451 25 118 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 118 156 2 12 59 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 118 156 (accept_3_5 23 118 156 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 118 156 2 11 59 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 118 156 (Polychromatic418967fa.accept_17_4_16_3_1_4620 21 118 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 118 156 2 10 59 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 118 156
  (Polychromatic418967fa.accept_15_4_13_6_1_642 19 118 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 118 156 2 9 59 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 118 156 (accept_3_5 17 118 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  118 156 2 8 59 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 118 156 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 118 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 118 156 2 7 59 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 118 156 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 118 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 118 156 2 6 59 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 118 156 (accept_3_5 11 118 156
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 118 156 2 5 59 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 118 156
  (Polychromatic418967fa.accept_18_9_10_12_1_5793 9 118 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 118 156 2 4 59 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 118 156 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 118 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 118 156 2 3 59 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 118 156 (accept_3_5 5 118 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 118 156 2 2 59 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 118 156 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 118 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 118 156 2 1 59 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 118 156 (Polychromatic418967fa.accept_7_1_6_2_1_18 1
  118 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118
  156))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 117 156 (Eq.refl Bool.true) (allA_succ_of_gcd 39 117 156 39
  1 3 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 117 156
  (Polychromatic418967fa.accept_7_3_5_2_1_17 38 117 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 117 156 (Polychromatic418967fa.accept_15_7_12_6_1_1327 37 117 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 117 156 3 12 39 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 117 156 (Polychromatic418967fa.accept_14_7_5_2_1_2473
  35 117 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 156
  (Polychromatic418967fa.accept_18_16_9_12_1_1182 34 117 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 33 117 156 3 11 39 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 32 117 156 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 117 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 156
  (Polychromatic418967fa.accept_7_3_5_2_1_17 31 117 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 117 156 3 10 39 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 117 156 (Polychromatic418967fa.accept_17_12_15_3_1_7168 29 117 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 156
  (Polychromatic418967fa.accept_18_10_9_12_1_3259 28 117 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 117 156 3 9 39 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 26 117 156 13 2 9 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 117 156 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 117 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 117 156 3 8 39 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 117 156
  (Polychromatic418967fa.accept_10_3_7_6_1_659 23 117 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 117 156 (Polychromatic418967fa.accept_15_7_12_6_1_1327 22 117 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 117 156 3 7 39 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 117 156 (Polychromatic418967fa.accept_11_9_7_2_1_1068
  20 117 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 156
  (Polychromatic418967fa.accept_20_19_17_16_1_2732 19 117 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 117 156 3 6 39 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 117 156 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 117 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 156
  (Polychromatic418967fa.accept_18_16_9_12_1_1182 16 117 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 117 156 3 5 39 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 117 156 (Polychromatic418967fa.accept_17_14_15_3_1_4618 14 117 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13 117 156 13 1 9 12 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 12 117 156 3 4 39 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 117 156
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 117 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 117 156 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 117 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 117 156 3 3 39 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 117 156 (Polychromatic418967fa.accept_16_8_5_12_1_3812 8 117 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 156
  (Polychromatic418967fa.accept_14_7_5_2_1_2473 7 117 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 117 156 3 2 39 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 117 156 (Polychromatic418967fa.accept_15_5_12_6_1_639 5 117 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 156 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 117 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 117 156 3 1 39 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 117 156
  (Polychromatic418967fa.accept_15_2_12_6_1_3063 2 117 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 117 156 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 117 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 117 156)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 116 156
  (Eq.refl Bool.true) (allA_succ_of_gcd 40 116 156 4 10 29 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 116 156 (Polychromatic418967fa.accept_15_9_11_6_1_637 39 116
  156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 116 156 2 19 58 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 116 156 (accept_3_4 37
  116 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 116 156 4 9 29 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 116 156
  (Polychromatic418967fa.accept_15_5_11_6_1_692 35 116 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 116 156 2 17 58 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 116 156 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 116 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 116 156 4 8 29 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 116 156 (accept_3_4 31 116 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 116 156 2 15 58 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 116 156 (Polychromatic418967fa.accept_9_2_8_3_1_181 29
  116 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 116 156 4 7 29 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 116 156
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 116 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 116 156 2 13 58 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 116 156 (accept_3_4 25 116 156 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 116 156 4 6 29 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 116 156 (Polychromatic418967fa.accept_9_5_8_3_1_437 23 116 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 116 156 2 11 58 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 116 156 (Polychromatic418967fa.accept_16_5_4_12_1_3800
  21 116 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 116 156 4 5 29 39
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 116 156
  (accept_3_4 19 116 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 116 156 2 9 58 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 116 156
  (Polychromatic418967fa.accept_15_2_11_6_1_2135 17 116 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 116 156 4 4 29 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 116 156 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 116 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 116 156 2 7 58 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 116 156 (accept_3_4 13 116 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 116 156 4 3 29 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 116 156 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 116 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 116 156 2 5 58 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 116 156
  (Polychromatic418967fa.accept_14_9_4_2_1_983 9 116 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 116 156 4 2 29 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 116 156 (accept_3_4 7 116 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 116
  156 2 3 58 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  116 156 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 116 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 116 156 4 1 29 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 116 156 (Polychromatic418967fa.accept_15_3_11_6_1_3083 3 116 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 116 156 2 1 58 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 116 156 (accept_3_4 1 116 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 116 156))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 115 156 (Eq.refl
  Bool.true) (allA_succ_of_accept 41 115 156 (accept_3_5 41 115 156 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 115 156 (Polychromatic418967fa.accept_7_5_3_2_1_249 40 115 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 115 156 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 115 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 115 156 (accept_3_5 38 115 156
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 115 156 (Polychromatic418967fa.accept_9_1_7_3_1_41 37
  115 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 115 156
  (Polychromatic418967fa.accept_7_1_3_2_1_13 36 115 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 115 156 (accept_3_5 35 115 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 115 156 (Polychromatic418967fa.accept_7_6_3_2_1_461 34 115 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 115 156 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 115 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 115 156 (accept_3_5 32 115 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 115 156 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 115 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 115 156
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 30 115 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 115 156 (accept_3_5 29 115 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 115 156 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 115 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 115 156 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 115 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 115 156 (accept_3_5 26 115 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 115 156 (Polychromatic418967fa.accept_16_9_3_12_1_1802 25 115 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 115 156
  (Polychromatic418967fa.accept_9_6_7_3_1_436 24 115 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 115 156 (accept_3_5 23 115 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 115 156 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 115 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 115 156 (Polychromatic418967fa.accept_10_1_5_6_1_649 21 115 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 115 156 (accept_3_5 20 115 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 115 156 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 115 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 115 156
  (Polychromatic418967fa.accept_15_3_10_6_1_632 18 115 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 115 156 (accept_3_5 17 115 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 115 156 (Polychromatic418967fa.accept_15_1_10_6_1_631 16 115 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 115 156 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 115 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 115 156 (accept_3_5 14 115 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 115 156 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 115 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 115 156
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 115 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 115 156 (accept_3_5 11 115 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 115 156 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 115 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 115 156 (Polychromatic418967fa.accept_10_9_5_6_1_691 9 115 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 115 156 (accept_3_5 8 115 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 115 156 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 115 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 115 156
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 115 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 115 156 (accept_3_5 5 115 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  115 156 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 115 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 115 156 (Polychromatic418967fa.accept_15_3_10_6_1_632 3 115 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 156 (accept_3_5 2 115 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 115 156 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 115 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115 156))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 43 114 156 (Eq.refl Bool.true) (allA_succ_of_gcd 42 114 156 6 7 19 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 114 156
  (Polychromatic418967fa.accept_9_5_6_3_1_40 41 114 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 114 156 2 20 57 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 114 156 3 13 38 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 114 156 2 19 57 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 114 156 (Polychromatic418967fa.accept_9_1_6_3_1_177 37 114 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 114 156 6 6 19 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 114 156
  (Polychromatic418967fa.accept_9_8_6_3_1_457 35 114 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 114 156 2 17 57 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 114 156 3 11 38 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 114 156 2 16 57 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 114 156 (Polychromatic418967fa.accept_9_4_6_3_1_179 31 114 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 114 156 6 5 19 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 114 156
  (Polychromatic418967fa.accept_9_2_6_3_1_178 29 114 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 114 156 2 14 57 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 27 114 156 3 9 38 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 114 156 2 13 57 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 114 156 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 114 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 114 156 6 4 19 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 114 156
  (Polychromatic418967fa.accept_9_5_6_3_1_40 23 114 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 114 156 2 11 57 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 114 156 3 7 38 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 114 156 2 10 57 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 114 156 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 114 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 114 156 6 3 19 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 114 156
  (Polychromatic418967fa.accept_9_8_6_3_1_457 17 114 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 114 156 2 8 57 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 114 156 3 5 38 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 114 156 2 7 57 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 114 156 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 114 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 114 156 6 2 19 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 114 156 (Polychromatic418967fa.accept_9_2_6_3_1_178 11
  114 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 114 156 2 5 57 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 114 156 3 3 38 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 114 156 2 4 57 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 114 156
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 114 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 114 156 6 1 19 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 114 156 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 114 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 114 156 2 2 57 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 114 156 3 1 38 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 114 156 2 1 57 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 156 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 114 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  156))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 113 156 (Eq.refl Bool.true) (allA_succ_of_accept 43 113
  156 (accept_3_4 43 113 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 113 156
  (Polychromatic418967fa.accept_9_6_5_3_1_205 42 113 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 113 156 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 113 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 113 156 (accept_3_4 40 113 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 113 156 (Polychromatic418967fa.accept_10_9_3_6_1_686 39 113 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 113 156
  (Polychromatic418967fa.accept_7_3_1_2_1_247 38 113 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 113 156 (accept_3_4 37 113 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 113 156 (Polychromatic418967fa.accept_14_8_1_2_1_965 36 113 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 113 156 (Polychromatic418967fa.accept_9_8_5_3_1_777 35 113 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 113 156 (accept_3_4 34 113 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 113 156 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 113 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 113 156
  (Polychromatic418967fa.accept_15_2_8_6_1_1340 32 113 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 113 156 (accept_3_4 31 113 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 113 156 (Polychromatic418967fa.accept_19_11_18_4_1_2957 30 113 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 113 156 (Polychromatic418967fa.accept_8_5_1_4_1_628 29 113 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 113 156 (accept_3_4 28 113 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 113 156 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 113 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 113 156
  (Polychromatic418967fa.accept_9_8_5_3_1_777 26 113 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 113 156 (accept_3_4 25 113 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 113 156 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 113 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 113 156 (Polychromatic418967fa.accept_11_1_3_2_1_1090 23 113 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 113 156 (accept_3_4 22 113 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 113 156 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 113 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 156
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 113 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 113 156 (accept_3_4 19 113 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 113 156 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 113 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 113 156 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 113 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 156 (accept_3_4 16 113 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 113 156 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 113 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 156
  (Polychromatic418967fa.accept_15_14_8_6_1_2133 14 113 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 113 156 (accept_3_4 13 113 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 113 156 (Polychromatic418967fa.accept_11_1_3_2_1_1090 12 113 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 113 156 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 113 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 156 (accept_3_4 10 113 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 156 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 113 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 156
  (Polychromatic418967fa.accept_9_8_5_3_1_777 8 113 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 113 156 (accept_3_4 7 113 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  113 156 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 113 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 113 156 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 113 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 156 (accept_3_4 4 113 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 156 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 113 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 156
  (Polychromatic418967fa.accept_9_2_5_3_1_37 2 113 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 156 (accept_3_4 1 113 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  156)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 112 156 (Eq.refl Bool.true) (allA_succ_of_gcd 44 112
  156 4 11 28 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43
  112 156 (Polychromatic418967fa.accept_9_7_4_3_1_204 43 112 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 112 156 2 21 56 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 112 156 (accept_3_5 41 112 156 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 112 156 4 10 28 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 112 156 (Polychromatic418967fa.accept_19_1_17_4_1_8520 39 112 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 112 156 2 19 56 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 112 156
  (Polychromatic418967fa.accept_9_1_4_3_1_201 37 112 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 112 156 4 9 28 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 112 156 (accept_3_5 35 112 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  112 156 2 17 56 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 112 156 (Polychromatic418967fa.accept_9_6_4_3_1_203 33 112 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 112 156 4 8 28 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 112 156 (Polychromatic418967fa.accept_10_1_2_6_1_638
  31 112 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 112 156 2 15 56 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 112 156
  (accept_3_5 29 112 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 112 156 4 7 28 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 112 156
  (Polychromatic418967fa.accept_15_12_7_6_1_4013 27 112 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 112 156 2 13 56 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 112 156 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 112 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 112 156 4 6 28 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 112 156 (accept_3_5 23 112 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 112 156 2 11 56 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 112 156 (Polychromatic418967fa.accept_10_1_2_6_1_638
  21 112 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 112 156 4 5 28 39
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 112 156
  (Polychromatic418967fa.accept_9_1_4_3_1_201 19 112 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 112 156 2 9 56 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 112 156 (accept_3_5 17 112 156 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  112 156 4 4 28 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 112 156 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 112 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 112 156 2 7 56 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 112 156 (Polychromatic418967fa.accept_15_13_7_6_1_682 13 112 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 112 156 4 3 28 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 112 156 (accept_3_5 11 112 156
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 112 156 2 5 56 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 112 156
  (Polychromatic418967fa.accept_17_9_10_3_1_3423 9 112 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 112 156 4 2 28 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 112 156 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 112 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 112 156 2 3 56 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 112 156 (accept_3_5 5 112 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 112 156 4 1 28 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 112 156 (Polychromatic418967fa.accept_21_3_7_9_1_8519 3 112 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 112 156 2 1 56 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 112 156 (Polychromatic418967fa.accept_9_1_4_3_1_201 1
  112 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112
  156))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 111 156 (Eq.refl Bool.true) (allA_succ_of_gcd 45 111
  156 3 15 37 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44
  111 156 (Polychromatic418967fa.accept_17_10_9_3_1_7144 44 111 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 111 156 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 111 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 111 156 3 14 37 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 111 156
  (Polychromatic418967fa.accept_19_3_16_4_1_7076 41 111 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 111 156 (Polychromatic418967fa.accept_16_8_15_12_1_1747 40 111 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 111 156 3 13 37 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 111 156
  (Polychromatic418967fa.accept_7_3_6_2_1_90 38 111 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 111 156 (Polychromatic418967fa.accept_10_7_1_6_1_673 37 111 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 111 156 3 12 37 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 111 156 (Polychromatic418967fa.accept_8_3_7_4_1_42 35
  111 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 111 156
  (Polychromatic418967fa.accept_16_2_15_12_1_1744 34 111 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 33 111 156 3 11 37 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 32 111 156 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 111 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 156
  (Polychromatic418967fa.accept_7_3_6_2_1_90 31 111 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 111 156 3 10 37 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 111 156 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 111 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 156
  (Polychromatic418967fa.accept_17_11_9_3_1_1463 28 111 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 111 156 3 9 37 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 111 156 (Polychromatic418967fa.accept_18_8_3_12_1_3247 26 111 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 156 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 111 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 111 156 3 8 37 52 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 111 156
  (Polychromatic418967fa.accept_17_6_9_3_1_704 23 111 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 111 156 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 111 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 111 156 3 7 37 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 111 156
  (Polychromatic418967fa.accept_16_4_15_12_1_1745 20 111 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 111 156 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 111 156 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 111 156 3 6 37 52 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 111 156
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 111 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 111 156 (Polychromatic418967fa.accept_21_16_6_9_1_8464 16 111 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 111 156 3 5 37 52 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 111 156 (Polychromatic418967fa.accept_11_3_1_2_1_1063
  14 111 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 156
  (Polychromatic418967fa.accept_16_13_15_12_1_1748 13 111 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 111 156 3 4 37 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 111 156 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 111 156 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 156
  (Polychromatic418967fa.accept_7_3_6_2_1_90 10 111 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 111 156 3 3 37 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 111 156 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 111 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 156 (Polychromatic418967fa.accept_10_7_1_6_1_673 7 111 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 111 156 3 2 37 52 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 111 156
  (Polychromatic418967fa.accept_10_5_1_6_1_672 5 111 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 111 156 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 111 156 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 111 156 3 1 37 52 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 111 156 (Polychromatic418967fa.accept_10_2_1_6_1_634 2 111 156
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 156
  (Polychromatic418967fa.accept_7_1_6_2_1_18 1 111 156 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 111 156))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_156_segment_000)))))))))))))))))))))))))))))))))))))))))))))


