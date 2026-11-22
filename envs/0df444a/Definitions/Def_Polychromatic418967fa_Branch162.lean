-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch162
-- name    : Polychromatic418967fa_Branch162
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:16:04.440378+00:00
-- url     : https://prove2.me/theorems/fb587c68-c7f8-4f25-b2f4-da7143d24132
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch162_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_162 : allB 162 162 :=
  allB_succ' 2 161 162 (Eq.refl Bool.true) (allA_succ_of_accept 1 161 162 (accept_3_4 1 161 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 161 162)) (allB_succ' 3 160 162 (Eq.refl Bool.true) (allA_succ_of_gcd 2 160 162 2 1 80
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 160 162
  (Polychromatic418967fa.accept_41_1_37_39_1_9020 1 160 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 160 162))) (allB_succ' 4 159 162 (Eq.refl Bool.true) (allA_succ_of_gcd 3 159 162 3 1 53 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 159 162
  (Polychromatic418967fa.accept_11_2_5_8_1_470 2 159 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 159 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 159 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 159 162)))) (allB_succ' 5 158 162 (Eq.refl Bool.true) (allA_succ_of_gcd 4
  158 162 2 2 79 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  3 158 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 158 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 158 162 2 1 79 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 158 162 (accept_3_4 1 158 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158
  162))))) (allB_succ' 6 157 162 (Eq.refl Bool.true) (allA_succ_of_accept 5 157 162 (accept_3_5 5 157 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 157 162 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 157 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 157 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 157 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 157 162 (accept_3_5 2 157 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  157 162 (Polychromatic418967fa.accept_21_1_10_15_1_2828 1 157 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 157 162)))))) (allB_succ' 7 156 162 (Eq.refl Bool.true) (allA_succ_of_gcd 6 156 162 6 1 26 27
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 156 162
  (Polychromatic418967fa.accept_11_5_2_8_1_866 5 156 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 156 162 2 2 78 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 156 162 3 1 52 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 156 162 2 1 78 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 156 162 (Polychromatic418967fa.accept_10_1_6_2_1_867 1 156 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 156 162))))))) (allB_succ' 8 155 162 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 155 162 (accept_3_4 7 155 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  155 162 (Polychromatic418967fa.accept_15_6_5_12_1_1642 6 155 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 155 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 155 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 155 162 (accept_3_4 4 155 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 155 162 (Polychromatic418967fa.accept_10_3_5_2_1_38 3 155 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 155 162
  (Polychromatic418967fa.accept_13_2_12_6_1_2394 2 155 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 155 162 (accept_3_4 1 155 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 155
  162)))))))) (allB_succ' 9 154 162 (Eq.refl Bool.true) (allA_succ_of_gcd 8 154 162 2 4 77 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 154 162
  (Polychromatic418967fa.accept_10_7_4_2_1_903 7 154 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 154 162 2 3 77 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 154 162 (accept_3_5 5 154 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 154
  162 2 2 77 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  154 162 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 154 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 154 162 2 1 77 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 154 162 (Polychromatic418967fa.accept_15_1_4_12_1_2401 1 154 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 154 162))))))))) (allB_succ' 10 153 162 (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 153 162 9 1 17 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 153 162 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 153 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 153 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 153 162 3 2 51 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 153 162
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 153 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 153 162 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 153 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 153 162 3 1 51 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 153 162 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 153 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 162
  (Polychromatic418967fa.accept_10_1_3_2_1_220 1 153 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 153 162)))))))))) (allB_succ' 11 152 162 (Eq.refl Bool.true) (allA_succ_of_gcd 10 152 162 2 5 76 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 152 162
  (Polychromatic418967fa.accept_12_9_8_6_1_466 9 152 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 152 162 2 4 76 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 152 162 (accept_3_4 7 152 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 152
  162 2 3 76 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  152 162 (Polychromatic418967fa.accept_15_5_2_12_1_2543 5 152 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 152 162 2 2 76 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 152 162 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 152 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 152 162 2 1 76 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 152 162 (accept_3_4 1 152 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 152 162))))))))))) (allB_succ' 12 151 162 (Eq.refl Bool.true) (allA_succ_of_accept 11
  151 162 (accept_3_5 11 151 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 151 162
  (Polychromatic418967fa.accept_7_3_4_1_1_71 10 151 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 151 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 151 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 151 162 (accept_3_5 8 151 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 151 162 (Polychromatic418967fa.accept_17_7_15_9_1_9019 7 151 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 151 162
  (Polychromatic418967fa.accept_10_6_1_2_1_874 6 151 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 151 162 (accept_3_5 5 151 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  151 162 (Polychromatic418967fa.accept_14_4_11_8_1_2034 4 151 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 151 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 151 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 151 162 (accept_3_5 2 151 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 151 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 151 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 151 162)))))))))))) (allB_succ' 13 150 162 (Eq.refl
  Bool.true) (allA_succ_of_gcd 12 150 162 6 2 25 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 150 162 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 150 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 150 162 2 5 75 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 150 162 3 3 50 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 150 162 2 4 75 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 150 162
  (Polychromatic418967fa.accept_19_7_17_10_1_4630 7 150 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 150 162 6 1 25 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 150 162 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 150 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 150 162 2 2 75 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 150 162 3 1 50 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 150 162 2 1 75 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 150 162 (Polychromatic418967fa.accept_13_1_7_6_1_142 1 150 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150 162))))))))))))) (allB_succ' 14 149 162
  (Eq.refl Bool.true) (allA_succ_of_accept 13 149 162 (accept_3_4 13 149 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 149 162 (Polychromatic418967fa.accept_20_12_9_2_1_4472 12 149 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 149 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 149 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 149 162 (accept_3_4 10 149 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 149 162 (Polychromatic418967fa.accept_15_9_14_12_1_913
  9 149 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 149 162
  (Polychromatic418967fa.accept_19_8_16_10_1_7484 8 149 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 149 162 (accept_3_4 7 149 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  149 162 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 149 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 149 162 (Polychromatic418967fa.accept_17_5_13_9_1_9018 5 149 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 149 162 (accept_3_4 4 149 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 149 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 149 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 149 162
  (Polychromatic418967fa.accept_15_2_14_12_1_2453 2 149 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 149 162 (accept_3_4 1 149 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 149
  162)))))))))))))) (allB_succ' 15 148 162 (Eq.refl Bool.true) (allA_succ_of_gcd 14 148 162 2 7 74 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 148 162
  (Polychromatic418967fa.accept_11_2_5_8_1_470 13 148 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 148 162 2 6 74 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 148 162 (accept_3_5 11 148 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  148 162 2 5 74 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 148 162 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 148 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 148 162 2 4 74 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 148 162 (Polychromatic418967fa.accept_21_7_1_15_1_680 7 148 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 148 162 2 3 74 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 148 162 (accept_3_5 5 148 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 148 162 2 2 74 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 148 162 (Polychromatic418967fa.accept_11_3_5_8_1_458 3 148 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 148 162 2 1 74 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 148 162
  (Polychromatic418967fa.accept_13_1_5_6_1_1048 1 148 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 148 162))))))))))))))) (allB_succ' 16 147 162 (Eq.refl Bool.true) (allA_succ_of_gcd 15 147 162 3 5 49 54
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 147 162
  (Polychromatic418967fa.accept_10_4_7_2_1_211 14 147 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 147 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 147 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 147 162 3 4 49 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 147 162 (Polychromatic418967fa.accept_13_11_4_6_1_1006
  11 147 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 147 162
  (Polychromatic418967fa.accept_12_10_3_6_1_882 10 147 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 147 162 3 3 49 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 147 162 (Polychromatic418967fa.accept_12_8_3_6_1_909 8 147 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 162 (Polychromatic418967fa.accept_11_7_4_8_1_1371 7 147 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 147 162 3 2 49 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 147 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 147 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 147 162 (Polychromatic418967fa.accept_10_4_7_2_1_211 4 147 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 147 162 3 1 49 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 147 162 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 147 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 147 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 147 162)))))))))))))))) (allB_succ' 17 146 162 (Eq.refl Bool.true) (allA_succ_of_gcd 16 146 162 2 8 73 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 146 162
  (Polychromatic418967fa.accept_12_3_2_6_1_138 15 146 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 146 162 2 7 73 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 146 162 (accept_3_4 13 146 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12
  146 162 2 6 73 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  11 146 162 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 146 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 146 162 2 5 73 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 146 162 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 146 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 146 162 2 4 73 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 146 162 (accept_3_4 7 146 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 146 162 2 3 73 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 146 162 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 146 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 146 162 2 2 73 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 146 162
  (Polychromatic418967fa.accept_12_3_2_6_1_138 3 146 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 146 162 2 1 73 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 146 162 (accept_3_4 1 146 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146
  162))))))))))))))))) (allB_succ' 18 145 162 (Eq.refl Bool.true) (allA_succ_of_accept 17 145 162 (accept_3_5 17 145 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 145 162 (Polychromatic418967fa.accept_11_5_2_8_1_866
  16 145 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 145 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 145 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 145 162 (accept_3_5 14 145 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 145 162 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 145 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 145 162 (Polychromatic418967fa.accept_13_12_2_6_1_2396 12 145 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 145 162 (accept_3_5 11 145 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 145 162 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 145 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 145 162
  (Polychromatic418967fa.accept_13_9_2_6_1_514 9 145 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 145 162 (accept_3_5 8 145 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  145 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 145 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 145 162 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 145 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 145 162 (accept_3_5 5 145 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 145 162 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 145 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 145 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 145 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 145 162 (accept_3_5 2 145 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  145 162 (Polychromatic418967fa.accept_13_1_2_6_1_515 1 145 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 145 162)))))))))))))))))) (allB_succ' 19 144 162 (Eq.refl Bool.true) (allA_succ_of_gcd 18 144
  162 18 1 8 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  144 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 144 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 144 162 2 8 72 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 15 144 162 3 5 48 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 14 144 162 2 7 72 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 144 162 (Polychromatic418967fa.accept_21_13_18_15_1_2837 13 144 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 144 162 6 2 24 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 144 162
  (Polychromatic418967fa.accept_14_11_4_8_1_664 11 144 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 144 162 2 5 72 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 144 162 9 1 16 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 144 162 2 4 72 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 144 162 (Polychromatic418967fa.accept_10_7_4_2_1_903 7 144 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 144 162 6 1 24 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 144 162 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 144 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 144 162 2 2 72 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 144 162 3 1 48 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 144 162 2 1 72 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 144 162
  (Polychromatic418967fa.accept_17_1_8_9_1_1810 1 144 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 144 162))))))))))))))))))) (allB_succ' 20 143 162 (Eq.refl Bool.true) (allA_succ_of_accept 19 143 162
  (accept_3_4 19 143 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 143 162
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 143 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 143 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 143 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 143 162 (accept_3_4 16 143 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 143 162 (Polychromatic418967fa.accept_10_5_3_2_1_899 15 143 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 143 162
  (Polychromatic418967fa.accept_21_14_17_15_1_9017 14 143 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 143 162 (accept_3_4 13 143 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 143 162 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 143 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 143 162 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 143 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 143 162 (accept_3_4 10 143 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 143 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 9
  143 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 143 162
  (Polychromatic418967fa.accept_21_8_17_15_1_2834 8 143 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 143 162 (accept_3_4 7 143 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  143 162 (Polychromatic418967fa.accept_21_6_17_15_1_2833 6 143 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 143 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 143 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 143 162 (accept_3_4 4 143 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 143 162 (Polychromatic418967fa.accept_15_3_8_12_1_900 3 143 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 143 162
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 143 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 143 162 (accept_3_4 1 143 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 143
  162)))))))))))))))))))) (allB_succ' 21 142 162 (Eq.refl Bool.true) (allA_succ_of_gcd 20 142 162 2 10 71 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 142 162
  (Polychromatic418967fa.accept_15_4_7_12_1_5538 19 142 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 142 162 2 9 71 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 142 162 (accept_3_5 17 142 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  142 162 2 8 71 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 142 162 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 142 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 142 162 2 7 71 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 142 162 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 142 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 142 162 2 6 71 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 142 162 (accept_3_5 11 142 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 142 162 2 5 71 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 142 162
  (Polychromatic418967fa.accept_11_9_10_8_1_444 9 142 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 142 162 2 4 71 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 142 162 (Polychromatic418967fa.accept_13_7_12_6_1_1039 7 142 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 142 162 2 3 71 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 142 162 (accept_3_5 5 142 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 142 162 2 2 71 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 142 162 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 142 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 142 162 2 1 71 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 142 162 (Polychromatic418967fa.accept_14_1_2_8_1_655 1
  142 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142 162)))))))))))))))))))))
  (allB_succ' 22 141 162 (Eq.refl Bool.true) (allA_succ_of_gcd 21 141 162 3 7 47 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 141 162
  (Polychromatic418967fa.accept_12_8_9_6_1_127 20 141 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 141 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 141 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 141 162 3 6 47 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 141 162 (Polychromatic418967fa.accept_13_4_11_6_1_1033
  17 141 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 141 162
  (Polychromatic418967fa.accept_10_6_1_2_1_874 16 141 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 141 162 3 5 47 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 141 162 (Polychromatic418967fa.accept_12_2_9_6_1_439 14 141 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 162 (Polychromatic418967fa.accept_10_3_1_2_1_521 13 141
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 141 162 3 4 47 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 141 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 141 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 141 162 (Polychromatic418967fa.accept_11_10_9_8_1_1974 10 141 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 141 162 3 3 47 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 141 162 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 141 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 141 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 141 162 3 2 47 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 141 162 (Polychromatic418967fa.accept_13_5_11_6_1_505 5 141 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 162 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 141 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 141 162 3 1 47 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 141 162
  (Polychromatic418967fa.accept_12_2_9_6_1_439 2 141 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 141 162 (Polychromatic418967fa.accept_22_1_9_8_1_8995 1 141 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 141 162)))))))))))))))))))))) (allB_succ' 23 140 162 (Eq.refl Bool.true)
  (allA_succ_of_gcd 22 140 162 2 11 70 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 140 162 (Polychromatic418967fa.accept_12_9_8_6_1_466 21 140 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 140 162 2 10 70 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 140 162 (accept_3_4 19 140 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 140 162 2 9 70 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 140 162 (Polychromatic418967fa.accept_13_4_10_6_1_989
  17 140 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 140 162 2 8 70 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 140 162
  (Polychromatic418967fa.accept_12_3_8_6_1_895 15 140 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 140 162 2 7 70 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 140 162 (accept_3_4 13 140 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12
  140 162 2 6 70 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  11 140 162 (Polychromatic418967fa.accept_25_11_15_12_1_3419 11 140 162 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 140 162 2 5 70 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 140 162 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 140 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 140 162 2 4 70 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 140 162 (accept_3_4 7 140 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 140 162 2 3 70 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 140 162 (Polychromatic418967fa.accept_13_5_10_6_1_2361
  5 140 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 140 162 2 2 70 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 140 162
  (Polychromatic418967fa.accept_12_3_8_6_1_895 3 140 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 140 162 2 1 70 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 140 162 (accept_3_4 1 140 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140
  162))))))))))))))))))))))) (allB_succ' 24 139 162 (Eq.refl Bool.true) (allA_succ_of_accept 23 139 162 (accept_3_5 23
  139 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 139 162
  (Polychromatic418967fa.accept_15_7_4_12_1_2530 22 139 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 139 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 139 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 139 162 (accept_3_5 20 139 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 139 162 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 139 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 139 162 (Polychromatic418967fa.accept_17_1_3_9_1_958
  18 139 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 139 162 (accept_3_5 17
  139 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 139 162
  (Polychromatic418967fa.accept_7_2_6_1_1_73 16 139 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 139 162 (Polychromatic418967fa.accept_11_4_7_8_1_1926 15 139 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 139 162 (accept_3_5 14 139 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 139 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 139 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 139 162 (Polychromatic418967fa.accept_7_5_6_1_1_407
  12 139 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 139 162 (accept_3_5 11
  139 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 139 162
  (Polychromatic418967fa.accept_13_10_9_6_1_1026 10 139 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 139 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 139 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 139 162 (accept_3_5 8 139 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 139 162 (Polychromatic418967fa.accept_10_7_9_2_1_1887 7 139 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 139 162 (Polychromatic418967fa.accept_16_6_11_2_1_6485
  6 139 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 139 162 (accept_3_5 5
  139 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 139 162
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 4 139 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 139 162 (Polychromatic418967fa.accept_13_3_9_6_1_502 3 139 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 139 162 (accept_3_5 2 139 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 139 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 139 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 139 162)))))))))))))))))))))))) (allB_succ' 25 138 162 (Eq.refl
  Bool.true) (allA_succ_of_gcd 24 138 162 6 4 23 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 138 162 (Polychromatic418967fa.accept_15_8_3_12_1_1657 23 138 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 138 162 2 11 69 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 138 162 3 7 46 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 138 162 2 10 69 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 138 162
  (Polychromatic418967fa.accept_21_19_12_15_1_7307 19 138 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 138 162 6 3 23 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 138 162 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 138 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 138 162 2 8 69 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 138 162 3 5 46 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 138 162 2 7 69 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 138 162
  (Polychromatic418967fa.accept_7_6_5_1_1_416 13 138 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 138 162 6 2 23 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 138 162 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 138 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 138 162 2 5 69 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 138 162 3 3 46 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 138 162 2 4 69 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 138 162 (Polychromatic418967fa.accept_15_7_3_12_1_365 7
  138 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 138 162 6 1 23 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 138 162
  (Polychromatic418967fa.accept_10_5_8_2_1_517 5 138 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 138 162 2 2 69 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 138 162 3 1 46 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 138 162 2 1 69 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 138 162 (Polychromatic418967fa.accept_13_1_8_6_1_1016 1 138 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 138 162))))))))))))))))))))))))) (allB_succ' 26 137 162 (Eq.refl Bool.true)
  (allA_succ_of_accept 25 137 162 (accept_3_4 25 137 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 137 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 137 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 137 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 137 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 137 162 (accept_3_4 22 137 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 137 162 (Polychromatic418967fa.accept_15_6_2_12_1_885 21 137 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 137 162
  (Polychromatic418967fa.accept_15_5_2_12_1_2543 20 137 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 137 162 (accept_3_4 19 137 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 137 162 (Polychromatic418967fa.accept_14_4_11_8_1_2034 18 137 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 137 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 137 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 137 162 (accept_3_4 16 137 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 137 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 137 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 137 162
  (Polychromatic418967fa.accept_10_4_7_2_1_211 14 137 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 137 162 (accept_3_4 13 137 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 137 162 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 137 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 137 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 137 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 137 162 (accept_3_4 10 137 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 137 162 (Polychromatic418967fa.accept_10_9_7_2_1_887 9 137 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 162
  (Polychromatic418967fa.accept_17_8_1_9_1_7738 8 137 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 137 162 (accept_3_4 7 137 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  137 162 (Polychromatic418967fa.accept_15_6_2_12_1_885 6 137 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 137 162 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 137 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 162 (accept_3_4 4 137 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 137 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 137 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 137 162
  (Polychromatic418967fa.accept_11_2_5_8_1_470 2 137 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 137 162 (accept_3_4 1 137 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 137
  162)))))))))))))))))))))))))) (allB_succ' 27 136 162 (Eq.refl Bool.true) (allA_succ_of_gcd 26 136 162 2 13 68 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 136 162
  (Polychromatic418967fa.accept_7_4_3_1_1_87 25 136 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 136 162 2 12 68 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 136 162 (accept_3_5 23 136 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 136 162 2 11 68 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 136 162 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 136 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 136 162 2 10 68 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 136 162
  (Polychromatic418967fa.accept_7_5_3_1_1_424 19 136 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 136 162 2 9 68 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 136 162 (accept_3_5 17 136 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  136 162 2 8 68 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 136 162 (Polychromatic418967fa.accept_12_3_4_6_1_434 15 136 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 136 162 2 7 68 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 136 162 (Polychromatic418967fa.accept_15_13_1_12_1_1638 13 136 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 136 162 2 6 68 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 136 162 (accept_3_5 11
  136 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 136 162 2 5 68 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 136 162
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 136 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 136 162 2 4 68 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 136 162 (Polychromatic418967fa.accept_11_7_4_8_1_1371 7 136 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 136 162 2 3 68 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 136 162 (accept_3_5 5 136 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 136 162 2 2 68 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 136 162 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 136 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 136 162 2 1 68 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 136 162 (Polychromatic418967fa.accept_10_1_6_2_1_867 1
  136 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 136 162)))))))))))))))))))))))))))
  (allB_succ' 28 135 162 (Eq.refl Bool.true) (allA_succ_of_gcd 27 135 162 27 1 5 6 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 135 162
  (Polychromatic418967fa.accept_12_2_3_6_1_112 26 135 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 135 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 135 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 135 162 3 8 45 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 135 162 (Polychromatic418967fa.accept_10_3_5_2_1_38 23
  135 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 135 162
  (Polychromatic418967fa.accept_12_10_3_6_1_882 22 135 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 135 162 3 7 45 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 135 162 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 135 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 135 162 (Polychromatic418967fa.accept_21_19_9_15_1_4217 19 135
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 135 162 9 2 15 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 135 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 135 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 135 162 (Polychromatic418967fa.accept_11_5_3_8_1_454 16 135 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 135 162 3 5 45 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 135 162 (Polychromatic418967fa.accept_12_2_3_6_1_112
  14 135 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 135 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 135 162 3 4 45 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 135 162 (Polychromatic418967fa.accept_13_11_5_6_1_519 11 135 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 135 162 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 135 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 135 162 9 1 15 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 135 162
  (Polychromatic418967fa.accept_10_8_5_2_1_881 8 135 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 135 162 (Polychromatic418967fa.accept_10_7_5_2_1_880 7 135 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 135 162 3 2 45 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 135 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 135 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 135 162
  (Polychromatic418967fa.accept_12_4_3_6_1_879 4 135 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 135 162 3 1 45 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 135 162 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 135 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 135 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135 162)))))))))))))))))))))))))))) (allB_succ'
  29 134 162 (Eq.refl Bool.true) (allA_succ_of_gcd 28 134 162 2 14 67 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 134 162 (Polychromatic418967fa.accept_10_7_4_2_1_903
  27 134 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 134 162 2 13 67 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 134 162
  (accept_3_4 25 134 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 134 162 2 12 67 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 134 162
  (Polychromatic418967fa.accept_13_10_4_6_1_3224 23 134 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 134 162 2 11 67 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 134 162 (Polychromatic418967fa.accept_12_9_2_6_1_455 21 134 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 134 162 2 10 67 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 134 162 (accept_3_4 19 134 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 134 162 2 9 67 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 134 162 (Polychromatic418967fa.accept_10_7_4_2_1_903
  17 134 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 134 162 2 8 67 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 134 162
  (Polychromatic418967fa.accept_12_3_2_6_1_138 15 134 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 134 162 2 7 67 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 134 162 (accept_3_4 13 134 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12
  134 162 2 6 67 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  11 134 162 (Polychromatic418967fa.accept_13_11_4_6_1_1006 11 134 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 134 162 2 5 67 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 134 162 (Polychromatic418967fa.accept_12_9_2_6_1_455 9 134 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 134 162 2 4 67 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 134 162 (accept_3_4 7 134 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 134 162 2 3 67 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 134 162 (Polychromatic418967fa.accept_11_5_2_8_1_866 5 134 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 134 162 2 2 67 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 134 162
  (Polychromatic418967fa.accept_12_3_2_6_1_138 3 134 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 134 162 2 1 67 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 134 162 (accept_3_4 1 134 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134
  162))))))))))))))))))))))))))))) (allB_succ' 30 133 162 (Eq.refl Bool.true) (allA_succ_of_accept 29 133 162
  (accept_3_5 29 133 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 133 162
  (Polychromatic418967fa.accept_26_2_3_6_1_5078 28 133 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 133 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 133 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 133 162 (accept_3_5 26 133 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 133 162 (Polychromatic418967fa.accept_10_5_3_2_1_899 25 133 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 133 162
  (Polychromatic418967fa.accept_21_3_7_15_1_4300 24 133 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 133 162 (accept_3_5 23 133 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 133 162 (Polychromatic418967fa.accept_13_9_3_6_1_1661 22 133 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 133 162 (Polychromatic418967fa.accept_10_1_3_2_1_220 21 133 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 133 162 (accept_3_5 20 133 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 133 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 133 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 133 162
  (Polychromatic418967fa.accept_13_5_3_6_1_3278 18 133 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 133 162 (accept_3_5 17 133 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 133 162 (Polychromatic418967fa.accept_15_1_13_12_1_347 16 133 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 133 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 133 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 133 162 (accept_3_5 14 133 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 133 162 (Polychromatic418967fa.accept_14_13_7_8_1_677 13 133 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 133 162
  (Polychromatic418967fa.accept_17_12_14_9_1_5079 12 133 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 133 162 (accept_3_5 11 133 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 133 162 (Polychromatic418967fa.accept_13_10_3_6_1_1003 10 133 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 133 162 (Polychromatic418967fa.accept_13_9_3_6_1_1661 9 133 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 133 162 (accept_3_5 8 133 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 133 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 7
  133 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 133 162
  (Polychromatic418967fa.accept_14_6_7_8_1_624 6 133 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 133 162 (accept_3_5 5 133 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  133 162 (Polychromatic418967fa.accept_11_4_1_8_1_1366 4 133 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 133 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 133 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 133 162 (accept_3_5 2 133 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 133 162 (Polychromatic418967fa.accept_10_1_3_2_1_220 1 133 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 133 162)))))))))))))))))))))))))))))) (allB_succ' 31 132
  162 (Eq.refl Bool.true) (allA_succ_of_gcd 30 132 162 6 5 22 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 132 162 (Polychromatic418967fa.accept_20_9_12_2_1_5935 29 132
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 132 162 2 14 66 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 132 162 3 9 44 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 132 162 2 13 66 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 132 162
  (Polychromatic418967fa.accept_13_12_2_6_1_2396 25 132 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 132 162 6 4 22 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 132 162 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 132 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 132 162 2 11 66 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 132 162 3 7 44 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 132 162 2 10 66 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 132 162
  (Polychromatic418967fa.accept_7_5_6_1_1_407 19 132 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 132 162 6 3 22 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 132 162 (Polychromatic418967fa.accept_13_4_2_6_1_1043 17 132 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 132 162 2 8 66 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 132 162 3 5 44 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 132 162 2 7 66 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 132 162
  (Polychromatic418967fa.accept_21_13_6_15_1_5818 13 132 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 132 162 6 2 22 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 132 162 (Polychromatic418967fa.accept_19_11_18_10_1_1148 11 132 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 132 162 2 5 66 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 132 162 3 3 44 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 132 162 2 4 66 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 132 162
  (Polychromatic418967fa.accept_14_7_6_8_1_2856 7 132 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 132 162 6 1 22 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 132 162 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 132 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 132 162 2 2 66 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 132 162 3 1 44 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 132 162 2 1 66 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 132 162 (Polychromatic418967fa.accept_13_1_2_6_1_515 1 132 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132 162)))))))))))))))))))))))))))))))
  (allB_succ' 32 131 162 (Eq.refl Bool.true) (allA_succ_of_accept 31 131 162 (accept_3_4 31 131 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 131 162 (Polychromatic418967fa.accept_21_9_5_15_1_5741 30 131 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 131 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 131 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 131 162 (accept_3_4 28 131 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 131 162 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 131 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 131 162 (Polychromatic418967fa.accept_10_6_1_2_1_874 26 131 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 131 162 (accept_3_4 25 131 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 131 162 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 131 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 131 162
  (Polychromatic418967fa.accept_10_3_1_2_1_521 23 131 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 131 162 (accept_3_4 22 131 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 131 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 131 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 131 162 (Polychromatic418967fa.accept_7_6_5_1_1_416 20 131 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 131 162 (accept_3_4 19 131 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 131 162 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 131 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 131 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 131 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 131 162 (accept_3_4 16 131 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 131 162 (Polychromatic418967fa.accept_13_2_1_6_1_2365 15 131 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 131 162 (Polychromatic418967fa.accept_15_14_11_12_1_4440 14 131 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 131 162 (accept_3_4 13 131 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 131 162 (Polychromatic418967fa.accept_19_12_17_10_1_7365 12
  131 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 131 162
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 131 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 131 162 (accept_3_4 10 131 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  131 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 131 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 131 162 (Polychromatic418967fa.accept_13_8_1_6_1_997 8 131 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 131 162 (accept_3_4 7 131 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 131 162 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 131 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 131 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 131 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 131 162 (accept_3_4 4 131 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  131 162 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 131 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 131 162 (Polychromatic418967fa.accept_13_2_1_6_1_2365 2 131 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 131 162 (accept_3_4 1 131 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 131 162)))))))))))))))))))))))))))))))) (allB_succ' 33 130 162 (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 130 162 2 16 65 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 130 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 130 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 130 162 2 15 65 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 130 162 (accept_3_5 29 130 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 130 162 2 14 65 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 130 162 (Polychromatic418967fa.accept_12_3_10_6_1_442
  27 130 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 130 162 2 13 65 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 130 162
  (Polychromatic418967fa.accept_14_11_4_8_1_664 25 130 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 130 162 2 12 65 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 130 162 (accept_3_5 23 130 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 130 162 2 11 65 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 130 162 (Polychromatic418967fa.accept_11_10_9_8_1_1974 21 130 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 130 162 2 10 65 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 130 162
  (Polychromatic418967fa.accept_7_5_4_1_1_412 19 130 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 130 162 2 9 65 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 130 162 (accept_3_5 17 130 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  130 162 2 8 65 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 130 162 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 130 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 130 162 2 7 65 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 130 162 (Polychromatic418967fa.accept_15_13_10_12_1_2503 13 130 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 130 162 2 6 65 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 130 162 (accept_3_5 11
  130 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 130 162 2 5 65 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 130 162
  (Polychromatic418967fa.accept_12_9_10_6_1_872 9 130 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 130 162 2 4 65 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 130 162 (Polychromatic418967fa.accept_15_7_10_12_1_2403 7 130 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 130 162 2 3 65 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 130 162 (accept_3_5 5 130 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 130 162 2 2 65 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 130 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 130 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 130 162 2 1 65 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 130 162 (Polychromatic418967fa.accept_19_1_16_10_1_6026
  1 130 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 130
  162))))))))))))))))))))))))))))))))) (allB_succ' 34 129 162 (Eq.refl Bool.true) (allA_succ_of_gcd 33 129 162 3 11 43
  54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 129 162
  (Polychromatic418967fa.accept_7_4_3_1_1_87 32 129 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 129 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 129 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 129 162 3 10 43 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 129 162
  (Polychromatic418967fa.accept_15_14_9_12_1_2498 29 129 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 129 162 (Polychromatic418967fa.accept_12_4_9_6_1_440 28 129 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 129 162 3 9 43 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 129 162
  (Polychromatic418967fa.accept_7_5_3_1_1_424 26 129 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 129 162 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 129 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 129 162 3 8 43 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 129 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 23
  129 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 162
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 129 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 129 162 3 7 43 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 129 162 (Polychromatic418967fa.accept_12_8_9_6_1_127 20 129 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 129 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 129 162 3 6 43 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 129 162
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 17 129 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 129 162 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 129 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 129 162 3 5 43 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 129 162 (Polychromatic418967fa.accept_12_2_9_6_1_439
  14 129 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 162
  (Polychromatic418967fa.accept_17_13_10_9_1_946 13 129 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 129 162 3 4 43 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 129 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 129 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 162 (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 129
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 129 162 3 3 43 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 129 162
  (Polychromatic418967fa.accept_12_8_9_6_1_127 8 129 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 129 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 129 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 129 162 3 2 43 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 129 162 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 129 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 162
  (Polychromatic418967fa.accept_7_4_3_1_1_87 4 129 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 129 162 3 1 43 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 129 162 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 129 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 162 (Polychromatic418967fa.accept_10_1_9_2_1_45 1 129 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129 162))))))))))))))))))))))))))))))))))
  (allB_succ' 35 128 162 (Eq.refl Bool.true) (allA_succ_of_gcd 34 128 162 2 17 64 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 128 162
  (Polychromatic418967fa.accept_12_9_8_6_1_466 33 128 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 128 162 2 16 64 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 128 162 (accept_3_4 31 128 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 128 162 2 15 64 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 128 162 (Polychromatic418967fa.accept_14_1_2_8_1_655 29 128 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 128 162 2 14 64 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 128 162
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 128 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 128 162 2 13 64 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 128 162 (accept_3_4 25 128 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 128 162 2 12 64 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 128 162 (Polychromatic418967fa.accept_19_4_14_10_1_7467 23 128 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 128 162 2 11 64 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 128 162
  (Polychromatic418967fa.accept_12_9_8_6_1_466 21 128 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 128 162 2 10 64 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 128 162 (accept_3_4 19 128 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 128 162 2 9 64 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 128 162 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 128 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 128 162 2 8 64 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 128 162 (Polychromatic418967fa.accept_10_5_8_2_1_517
  15 128 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 128 162 2 7 64 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 128 162
  (accept_3_4 13 128 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 128 162 2 6 64 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 128 162
  (Polychromatic418967fa.accept_15_11_8_12_1_4437 11 128 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 128 162 2 5 64 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 128 162 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 128 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 128 162 2 4 64 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 128 162 (accept_3_4 7 128 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 128 162 2 3 64 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 128 162 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 128 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 128 162 2 2 64 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 128 162
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 128 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 128 162 2 1 64 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 128 162 (accept_3_4 1 128 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128
  162))))))))))))))))))))))))))))))))))) (allB_succ' 36 127 162 (Eq.refl Bool.true) (allA_succ_of_accept 35 127 162
  (accept_3_5 35 127 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 127 162
  (Polychromatic418967fa.accept_10_4_7_2_1_211 34 127 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 127 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 127 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 127 162 (accept_3_5 32 127 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 127 162 (Polychromatic418967fa.accept_13_5_10_6_1_2361 31 127 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 127 162
  (Polychromatic418967fa.accept_13_4_10_6_1_989 30 127 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 127 162 (accept_3_5 29 127 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 127 162 (Polychromatic418967fa.accept_13_2_10_6_1_1676 28 127 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 127 162 (Polychromatic418967fa.accept_21_6_1_15_1_9016 27 127 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 127 162 (accept_3_5 26 127 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 127 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 127 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 127 162
  (Polychromatic418967fa.accept_10_4_7_2_1_211 24 127 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 127 162 (accept_3_5 23 127 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 127 162 (Polychromatic418967fa.accept_13_9_10_6_1_1028 22 127 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 127 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 127 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 127 162 (accept_3_5 20 127 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 127 162 (Polychromatic418967fa.accept_10_9_7_2_1_887 19 127 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 127 162
  (Polychromatic418967fa.accept_13_5_10_6_1_2361 18 127 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 127 162 (accept_3_5 17 127 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 127 162 (Polychromatic418967fa.accept_13_3_10_6_1_2382 16 127 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 127 162 (Polychromatic418967fa.accept_10_5_7_2_1_516 15 127 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 127 162 (accept_3_5 14 127 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 127 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 127 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 127 162
  (Polychromatic418967fa.accept_13_12_10_6_1_3212 12 127 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 127 162 (accept_3_5 11 127 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 127 162 (Polychromatic418967fa.accept_15_10_7_12_1_2490 10 127 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 127 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 9
  127 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 127 162 (accept_3_5 8 127
  162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 127 162
  (Polychromatic418967fa.accept_14_7_1_8_1_2873 7 127 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 127 162 (Polychromatic418967fa.accept_15_6_7_12_1_869 6 127 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 127 162 (accept_3_5 5 127 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 127 162 (Polychromatic418967fa.accept_10_4_7_2_1_211 4 127 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 127 162 (Polychromatic418967fa.accept_11_3_6_8_1_1924
  3 127 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 127 162 (accept_3_5 2
  127 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 127 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 127 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 127 162)))))))))))))))))))))))))))))))))))) (allB_succ' 37 126 162 (Eq.refl Bool.true) (allA_succ_of_gcd 36
  126 162 18 2 7 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  35 126 162 (Polychromatic418967fa.accept_11_2_5_8_1_470 35 126 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 126 162 2 17 63 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 33 126 162 3 11 42 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 126 162 2 16 63 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 126 162 (Polychromatic418967fa.accept_10_1_6_2_1_867
  31 126 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 126 162 6 5 21 27
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 126 162
  (Polychromatic418967fa.accept_13_3_9_6_1_502 29 126 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 126 162 2 14 63 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 27 126 162 9 3 14 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 126 162 2 13 63 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 126 162 (Polychromatic418967fa.accept_11_3_5_8_1_458 25 126 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 126 162 6 4 21 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 126 162
  (Polychromatic418967fa.accept_13_10_9_6_1_1026 23 126 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 126 162 2 11 63 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 126 162 3 7 42 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 126 162 2 10 63 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 126 162 (Polychromatic418967fa.accept_17_2_7_9_1_2796 19 126 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 126 162 18 1 7 9 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 126 162
  (Polychromatic418967fa.accept_13_4_9_6_1_2376 17 126 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 126 162 2 8 63 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 126 162 3 5 42 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 126 162 2 7 63 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 126 162 (Polychromatic418967fa.accept_11_2_5_8_1_470 13 126 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 126 162 6 2 21 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 126 162 (Polychromatic418967fa.accept_10_1_6_2_1_867
  11 126 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 126 162 2 5 63 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 126 162 9 1 14 18
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 126 162 2 4 63 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 126 162
  (Polychromatic418967fa.accept_13_7_9_6_1_148 7 126 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 126 162 6 1 21 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 126 162 (Polychromatic418967fa.accept_15_5_6_12_1_916 5 126 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 126 162 2 2 63 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 126 162 3 1 42 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 126 162 2 1 63 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 126 162 (Polychromatic418967fa.accept_10_1_6_2_1_867 1 126 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126 162)))))))))))))))))))))))))))))))))))))
  (allB_succ' 38 125 162 (Eq.refl Bool.true) (allA_succ_of_accept 37 125 162 (accept_3_4 37 125 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 125 162 (Polychromatic418967fa.accept_15_6_5_12_1_1642 36 125 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 125 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 125 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 125 162 (accept_3_4 34 125 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 125 162 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 125 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 125 162 (Polychromatic418967fa.accept_15_2_5_12_1_369 32 125 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 125 162 (accept_3_4 31 125 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 125 162 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 125 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 125 162
  (Polychromatic418967fa.accept_11_7_4_8_1_1371 29 125 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 125 162 (accept_3_4 28 125 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 125 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 125 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 125 162 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 125 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 125 162 (accept_3_4 25 125 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 125 162 (Polychromatic418967fa.accept_13_11_8_6_1_1023 24 125 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 125 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 125 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 125 162 (accept_3_4 22 125 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 125 162 (Polychromatic418967fa.accept_14_7_13_8_1_2067 21 125 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 125 162 (Polychromatic418967fa.accept_17_3_6_9_1_2761 20 125 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 125 162 (accept_3_4 19 125 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 125 162 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 125
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 125 162
  (Polychromatic418967fa.accept_10_7_5_2_1_880 17 125 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 125 162 (accept_3_4 16 125 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 125 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 125 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 125 162 (Polychromatic418967fa.accept_13_1_8_6_1_1016 14 125 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 125 162 (accept_3_4 13 125 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 125 162 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 125 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 125 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 125 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 125 162 (accept_3_4 10 125 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  125 162 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 125 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 125 162 (Polychromatic418967fa.accept_10_8_5_2_1_881 8 125 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 125 162 (accept_3_4 7 125 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 125 162 (Polychromatic418967fa.accept_15_6_5_12_1_1642 6 125 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 125 162
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 125 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 125 162 (accept_3_4 4 125 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  125 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 125 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 125 162 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 125 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 125 162 (accept_3_4 1 125 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 125 162)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 124 162 (Eq.refl
  Bool.true) (allA_succ_of_gcd 38 124 162 2 19 62 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 124 162 (Polychromatic418967fa.accept_10_7_4_2_1_903 37 124 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 124 162 2 18 62 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 124 162 (accept_3_5 35 124 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 124 162 2 17 62 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 124 162
  (Polychromatic418967fa.accept_12_9_4_6_1_460 33 124 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 124 162 2 16 62 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 124 162 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 124 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 124 162 2 15 62 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 124 162 (accept_3_5 29 124 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 124 162 2 14 62 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 124 162 (Polychromatic418967fa.accept_7_6_5_1_1_416 27
  124 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 124 162 2 13 62 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 124 162
  (Polychromatic418967fa.accept_7_4_5_1_1_418 25 124 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 124 162 2 12 62 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 124 162 (accept_3_5 23 124 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 124 162 2 11 62 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 124 162 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 124 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 124 162 2 10 62 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 124 162
  (Polychromatic418967fa.accept_20_19_4_2_1_8946 19 124 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 124 162 2 9 62 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 124 162 (accept_3_5 17 124 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  124 162 2 8 62 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 124 162 (Polychromatic418967fa.accept_12_3_4_6_1_434 15 124 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 124 162 2 7 62 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 124 162 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 124 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 124 162 2 6 62 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 124 162 (accept_3_5 11 124 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 124 162 2 5 62 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 124 162
  (Polychromatic418967fa.accept_12_9_4_6_1_460 9 124 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 124 162 2 4 62 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 124 162 (Polychromatic418967fa.accept_10_7_4_2_1_903 7 124 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 124 162 2 3 62 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 124 162 (accept_3_5 5 124 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 124 162 2 2 62 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 124 162 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 124 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 124 162 2 1 62 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 124 162 (Polychromatic418967fa.accept_13_1_7_6_1_142 1
  124 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 124
  162))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 123 162 (Eq.refl Bool.true) (allA_succ_of_gcd 39 123 162 3
  13 41 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 123
  162 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 123 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 123 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 123 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 123 162 3 12 41 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 123 162 (Polychromatic418967fa.accept_10_5_3_2_1_899
  35 123 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 123 162
  (Polychromatic418967fa.accept_12_10_3_6_1_882 34 123 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 123 162 3 11 41 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 123 162 (Polychromatic418967fa.accept_12_8_3_6_1_909 32 123 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 31
  123 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 123 162 3 10 41 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 123 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 123 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 123 162 (Polychromatic418967fa.accept_12_4_3_6_1_879 28 123 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 123 162 3 9 41 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 123 162 (Polychromatic418967fa.accept_7_5_4_1_1_412 26
  123 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 123 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 123 162 3 8 41 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 123 162 (Polychromatic418967fa.accept_15_8_3_12_1_1657 23 123 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 123 162 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 123
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 123 162 3 7 41 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 123 162
  (Polychromatic418967fa.accept_12_8_3_6_1_909 20 123 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 123 162 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 123 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 123 162 3 6 41 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 123 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 17
  123 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 123 162
  (Polychromatic418967fa.accept_11_5_2_8_1_866 16 123 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 123 162 3 5 41 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 123 162 (Polychromatic418967fa.accept_12_2_3_6_1_112 14 123 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 123 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 123 162 3 4 41 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 123 162
  (Polychromatic418967fa.accept_10_1_3_2_1_220 11 123 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 123 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 123 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 123 162 3 3 41 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 123 162 (Polychromatic418967fa.accept_12_8_3_6_1_909 8 123 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 162
  (Polychromatic418967fa.accept_15_7_3_12_1_365 7 123 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 123 162 3 2 41 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 123 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 123 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 162 (Polychromatic418967fa.accept_12_4_3_6_1_879 4 123 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 123 162 3 1 41 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 123 162
  (Polychromatic418967fa.accept_12_2_3_6_1_112 2 123 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 123 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 123 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 123 162)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 122 162
  (Eq.refl Bool.true) (allA_succ_of_gcd 40 122 162 2 20 61 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 122 162 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 122 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 122 162 2 19 61 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 122 162 (accept_3_4 37
  122 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 122 162 2 18 61 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 122 162
  (Polychromatic418967fa.accept_15_5_2_12_1_2543 35 122 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 122 162 2 17 61 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 122 162 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 122 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 122 162 2 16 61 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 122 162 (accept_3_4 31 122 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 122 162 2 15 61 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 122 162 (Polychromatic418967fa.accept_13_3_5_6_1_3192
  29 122 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 122 162 2 14 61 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 122 162
  (Polychromatic418967fa.accept_12_3_2_6_1_138 27 122 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 122 162 2 13 61 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 122 162 (accept_3_4 25 122 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 122 162 2 12 61 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 122 162 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 122 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 122 162 2 11 61 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 122 162
  (Polychromatic418967fa.accept_12_9_2_6_1_455 21 122 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 122 162 2 10 61 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 122 162 (accept_3_4 19 122 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 122 162 2 9 61 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 122 162 (Polychromatic418967fa.accept_13_4_5_6_1_3201 17 122 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 122 162 2 8 61 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 122 162 (Polychromatic418967fa.accept_11_4_1_8_1_1366
  15 122 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 122 162 2 7 61 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 122 162
  (accept_3_4 13 122 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 122 162 2 6 61 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 122 162
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 122 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 122 162 2 5 61 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 122 162 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 122 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 122 162 2 4 61 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 122 162 (accept_3_4 7 122 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 122 162 2 3 61 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 122 162 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 122 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 122 162 2 2 61 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 122 162 (Polychromatic418967fa.accept_12_3_2_6_1_138 3
  122 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 122 162 2 1 61 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 122 162 (accept_3_4 1
  122 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122 162)))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 42 121 162 (Eq.refl Bool.true) (allA_succ_of_accept 41 121 162 (accept_3_5 41 121 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 121 162 (Polychromatic418967fa.accept_34_6_19_26_1_9015 40 121 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 121 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 121 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 121 162 (accept_3_5 38 121 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 121 162 (Polychromatic418967fa.accept_13_11_4_6_1_1006 37 121 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 121 162 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 121 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 121 162 (accept_3_5 35 121 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 121 162 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 121 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 121 162
  (Polychromatic418967fa.accept_10_3_1_2_1_521 33 121 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 121 162 (accept_3_5 32 121 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 121 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 121 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 121 162 (Polychromatic418967fa.accept_21_9_16_15_1_9014 30 121 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 121 162 (accept_3_5 29 121 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 121 162 (Polychromatic418967fa.accept_13_2_4_6_1_2356 28 121
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 121 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 121 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 121 162 (accept_3_5 26 121 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 121 162 (Polychromatic418967fa.accept_22_3_11_8_1_9013 25 121 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 121 162 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 121 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 121 162 (accept_3_5 23 121 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 121 162 (Polychromatic418967fa.accept_13_9_4_6_1_1005 22 121 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 121 162
  (Polychromatic418967fa.accept_17_4_2_9_1_3896 21 121 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 121 162 (accept_3_5 20 121 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 121 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 121 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 121 162 (Polychromatic418967fa.accept_13_5_4_6_1_2371 18 121 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 121 162 (accept_3_5 17 121 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 121 162 (Polychromatic418967fa.accept_10_6_1_2_1_874 16 121
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 121 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 121 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 121 162 (accept_3_5 14 121 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 121 162 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 121 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 121 162 (Polychromatic418967fa.accept_16_12_9_2_1_8989 12 121 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 121 162 (accept_3_5 11 121 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 121 162 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 121 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 121 162
  (Polychromatic418967fa.accept_10_9_1_2_1_522 9 121 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 121 162 (accept_3_5 8 121 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  121 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 121 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 121 162 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 121 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 121 162 (accept_3_5 5 121 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 121 162 (Polychromatic418967fa.accept_15_4_1_12_1_914 4 121 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 121 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 121 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 121 162 (accept_3_5 2 121 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  121 162 (Polychromatic418967fa.accept_14_1_9_8_1_2863 1 121 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 121 162)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 120 162 (Eq.refl Bool.true)
  (allA_succ_of_gcd 42 120 162 6 7 20 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 120 162 (Polychromatic418967fa.accept_22_19_10_8_1_9011 41 120 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 120 162 2 20 60 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 120 162 3 13 40 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 120 162 2 19 60 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 120 162
  (Polychromatic418967fa.accept_17_3_1_9_1_9012 37 120 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 120 162 6 6 20 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 120 162 (Polychromatic418967fa.accept_13_9_3_6_1_1661 35 120 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 120 162 2 17 60 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 120 162 3 11 40 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 120 162 2 16 60 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 120 162
  (Polychromatic418967fa.accept_11_9_10_8_1_444 31 120 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 120 162 6 5 20 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 120 162 (Polychromatic418967fa.accept_22_7_10_8_1_9009 29 120 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 120 162 2 14 60 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 120 162 3 9 40 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 120 162 2 13 60 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 120 162
  (Polychromatic418967fa.accept_17_8_1_9_1_7738 25 120 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 120 162 6 4 20 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 120 162 (Polychromatic418967fa.accept_13_10_3_6_1_1003 23 120 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 120 162 2 11 60 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 120 162 3 7 40 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 120 162 2 10 60 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 120 162
  (Polychromatic418967fa.accept_22_19_10_8_1_9011 19 120 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 120 162 6 3 20 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 120 162 (Polychromatic418967fa.accept_25_17_20_12_1_8994 17 120 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 120 162 2 8 60 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 120 162 3 5 40 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 120 162 2 7 60 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 120 162
  (Polychromatic418967fa.accept_19_13_6_10_1_7395 13 120 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 120 162 6 2 20 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 120 162 (Polychromatic418967fa.accept_22_11_10_8_1_9010 11 120 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 120 162 2 5 60 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 120 162 3 3 40 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 120 162 2 4 60 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 120 162
  (Polychromatic418967fa.accept_22_7_10_8_1_9009 7 120 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 120 162 6 1 20 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 120 162 (Polychromatic418967fa.accept_13_5_3_6_1_3278 5 120 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 120 162 2 2 60 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 120 162 3 1 40 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 120 162 2 1 60 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 120 162 (Polychromatic418967fa.accept_13_1_3_6_1_158 1 120 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  162))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 119 162 (Eq.refl Bool.true) (allA_succ_of_accept 43 119
  162 (accept_3_4 43 119 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 119 162
  (Polychromatic418967fa.accept_23_19_4_1_1_9008 42 119 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 119 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 119 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 119 162 (accept_3_4 40 119 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 119 162 (Polychromatic418967fa.accept_15_9_14_12_1_913 39 119 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 119 162
  (Polychromatic418967fa.accept_13_12_2_6_1_2396 38 119 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 119 162 (accept_3_4 37 119 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 119 162 (Polychromatic418967fa.accept_13_10_2_6_1_1044 36 119 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 119 162 (Polychromatic418967fa.accept_13_9_2_6_1_514 35 119 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 119 162 (accept_3_4 34 119 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 119 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 119 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 119 162
  (Polychromatic418967fa.accept_11_10_9_8_1_1974 32 119 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 119 162 (accept_3_4 31 119 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 119 162 (Polychromatic418967fa.accept_13_4_2_6_1_1043 30 119 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 119 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 119 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 119 162 (accept_3_4 28 119 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 119 162 (Polychromatic418967fa.accept_10_7_9_2_1_1887 27 119 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 119 162
  (Polychromatic418967fa.accept_15_11_14_12_1_2458 26 119 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 119 162 (accept_3_4 25 119 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 119 162 (Polychromatic418967fa.accept_15_9_14_12_1_913 24 119 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 119 162 (Polychromatic418967fa.accept_13_10_2_6_1_1044 23 119
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 119 162 (accept_3_4 22 119
  162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 119 162 (Polychromatic418967fa.accept_4_1_3_2_1_3
  21 119 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 119 162
  (Polychromatic418967fa.accept_14_6_7_8_1_624 20 119 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 119 162 (accept_3_4 19 119 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 119 162 (Polychromatic418967fa.accept_19_18_5_10_1_2175 18 119 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 119 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 119 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 119 162 (accept_3_4 16 119 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 119 162 (Polychromatic418967fa.accept_14_1_7_8_1_2063 15 119 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 119 162
  (Polychromatic418967fa.accept_13_1_2_6_1_515 14 119 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 119 162 (accept_3_4 13 119 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 119 162 (Polychromatic418967fa.accept_13_12_2_6_1_2396 12 119 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 119 162 (Polychromatic418967fa.accept_10_1_9_2_1_45 11 119 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 162 (accept_3_4 10 119 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 119 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 119 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 162
  (Polychromatic418967fa.accept_13_8_2_6_1_2385 8 119 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 119 162 (accept_3_4 7 119 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  119 162 (Polychromatic418967fa.accept_14_6_7_8_1_624 6 119 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 119 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 119 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 162 (accept_3_4 4 119 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 119 162 (Polychromatic418967fa.accept_19_3_5_10_1_6033 3 119 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 162
  (Polychromatic418967fa.accept_15_2_14_12_1_2453 2 119 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 119 162 (accept_3_4 1 119 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  162)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 118 162 (Eq.refl Bool.true) (allA_succ_of_gcd 44 118
  162 2 22 59 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43
  118 162 (Polychromatic418967fa.accept_16_11_6_2_1_4155 43 118 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 118 162 2 21 59 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 118 162 (accept_3_5 41 118 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 118 162 2 20 59 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 118 162 (Polychromatic418967fa.accept_12_3_10_6_1_442 39 118 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 118 162 2 19 59 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 118 162
  (Polychromatic418967fa.accept_7_2_6_1_1_73 37 118 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 118 162 2 18 59 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 118 162 (accept_3_5 35 118 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 118 162 2 17 59 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 118 162 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 118 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 118 162 2 16 59 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 118 162
  (Polychromatic418967fa.accept_13_5_1_6_1_2367 31 118 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 118 162 2 15 59 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 118 162 (accept_3_5 29 118 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 118 162 2 14 59 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 118 162 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 118 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 118 162 2 13 59 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 118 162
  (Polychromatic418967fa.accept_10_5_8_2_1_517 25 118 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 118 162 2 12 59 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 118 162 (accept_3_5 23 118 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 118 162 2 11 59 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 118 162 (Polychromatic418967fa.accept_12_9_10_6_1_872 21 118 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 118 162 2 10 59 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 118 162
  (Polychromatic418967fa.accept_7_5_6_1_1_407 19 118 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 118 162 2 9 59 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 118 162 (accept_3_5 17 118 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  118 162 2 8 59 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 118 162 (Polychromatic418967fa.accept_10_5_8_2_1_517 15 118 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 118 162 2 7 59 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 118 162 (Polychromatic418967fa.accept_17_13_16_9_1_5128 13 118 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 118 162 2 6 59 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 118 162 (accept_3_5 11
  118 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 118 162 2 5 59 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 118 162
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 118 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 118 162 2 4 59 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 118 162 (Polychromatic418967fa.accept_13_7_1_6_1_3287 7 118 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 118 162 2 3 59 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 118 162 (accept_3_5 5 118 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 118 162 2 2 59 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 118 162 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 118 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 118 162 2 1 59 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 118 162 (Polychromatic418967fa.accept_15_1_13_12_1_347
  1 118 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118
  162))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 117 162 (Eq.refl Bool.true) (allA_succ_of_gcd 45 117
  162 9 5 13 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44
  117 162 (Polychromatic418967fa.accept_10_4_7_2_1_211 44 117 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 117 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 117 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 117 162 3 14 39 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 117 162
  (Polychromatic418967fa.accept_7_6_5_1_1_416 41 117 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 117 162 (Polychromatic418967fa.accept_12_4_9_6_1_440 40 117 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 117 162 3 13 39 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 117 162 (Polychromatic418967fa.accept_7_3_5_1_1_72 38
  117 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 162
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 37 117 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 117 162 9 4 13 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 117 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 117 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 162 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 117 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 117 162 3 11 39 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 117 162
  (Polychromatic418967fa.accept_7_4_5_1_1_418 32 117 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 117 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 117 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 117 162 3 10 39 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 117 162 (Polychromatic418967fa.accept_10_9_7_2_1_887
  29 117 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 162
  (Polychromatic418967fa.accept_12_4_9_6_1_440 28 117 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 117 162 9 3 13 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 117 162 (Polychromatic418967fa.accept_11_4_7_8_1_1926 26 117 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 162 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 117 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 117 162 3 8 39 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 117 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 117 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 117 162 (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 117 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 117 162 3 7 39 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 117 162 (Polychromatic418967fa.accept_7_6_5_1_1_416 20
  117 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 117 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 117 162 9 2 13 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 117 162 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 117 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 162 (Polychromatic418967fa.accept_12_4_9_6_1_440 16 117
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 117 162 3 5 39 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 117 162
  (Polychromatic418967fa.accept_10_4_7_2_1_211 14 117 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 117 162 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 117 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 117 162 3 4 39 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 117 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 11
  117 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 162
  (Polychromatic418967fa.accept_7_3_5_1_1_72 10 117 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 117 162 9 1 13 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 117 162 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 117 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 117 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 117 162 3 2 39 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 117 162
  (Polychromatic418967fa.accept_10_5_7_2_1_516 5 117 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 117 162 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 117 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 117 162 3 1 39 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 117 162 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 117 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 162
  (Polychromatic418967fa.accept_17_1_15_9_1_1743 1 117 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 117 162)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 116 162 (Eq.refl Bool.true)
  (allA_succ_of_gcd 46 116 162 2 23 58 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 116 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 116 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 116 162 2 22 58 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 116 162 (accept_3_4 43 116 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 116 162 2 21 58 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 116 162 (Polychromatic418967fa.accept_10_1_6_2_1_867
  41 116 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 116 162 2 20 58 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 116 162
  (Polychromatic418967fa.accept_12_3_8_6_1_895 39 116 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 116 162 2 19 58 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 116 162 (accept_3_4 37 116 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 116 162 2 18 58 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 116 162 (Polychromatic418967fa.accept_25_10_16_12_1_9007 35 116 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 116 162 2 17 58 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 116 162
  (Polychromatic418967fa.accept_7_5_4_1_1_412 33 116 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 116 162 2 16 58 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 116 162 (accept_3_4 31 116 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 116 162 2 15 58 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 116 162 (Polychromatic418967fa.accept_15_14_11_12_1_4440 29 116 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 116 162 2 14 58 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 116 162
  (Polychromatic418967fa.accept_12_3_8_6_1_895 27 116 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 116 162 2 13 58 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 116 162 (accept_3_4 25 116 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 116 162 2 12 58 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 116 162 (Polychromatic418967fa.accept_13_10_12_6_1_991 23 116 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 116 162 2 11 58 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 116 162
  (Polychromatic418967fa.accept_10_1_6_2_1_867 21 116 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 116 162 2 10 58 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 116 162 (accept_3_4 19 116 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 116 162 2 9 58 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 116 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 116 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 116 162 2 8 58 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 116 162 (Polychromatic418967fa.accept_12_3_8_6_1_895
  15 116 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 116 162 2 7 58 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 116 162
  (accept_3_4 13 116 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 116 162 2 6 58 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 116 162
  (Polychromatic418967fa.accept_10_1_6_2_1_867 11 116 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 116 162 2 5 58 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 116 162 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 116 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 116 162 2 4 58 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 116 162 (accept_3_4 7 116 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 116 162 2 3 58 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 116 162 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 116 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 116 162 2 2 58 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 116 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 3
  116 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 116 162 2 1 58 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 116 162 (accept_3_4 1
  116 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116 162)))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 48 115 162 (Eq.refl Bool.true) (allA_succ_of_accept 47 115 162 (accept_3_5 47 115 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 115 162 (Polychromatic418967fa.accept_7_4_3_1_1_87 46 115 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 115 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 115 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 115 162 (accept_3_5 44 115 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 115 162 (Polychromatic418967fa.accept_10_3_5_2_1_38 43 115 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 115 162 (Polychromatic418967fa.accept_19_4_1_10_1_7447 42 115 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 115 162 (accept_3_5 41 115 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 115 162 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 115 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 115 162
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 115 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 115 162 (accept_3_5 38 115 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 115 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 115 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 115 162 (Polychromatic418967fa.accept_11_3_5_8_1_458 36 115 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 115 162 (accept_3_5 35 115 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 115 162 (Polychromatic418967fa.accept_13_8_11_6_1_1035 34 115
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 115 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 115 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 115 162 (accept_3_5 32 115 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 115 162 (Polychromatic418967fa.accept_13_5_11_6_1_505 31 115 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 115 162 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 115 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 115 162 (accept_3_5 29 115 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 115 162 (Polychromatic418967fa.accept_10_8_5_2_1_881 28 115 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 115 162
  (Polychromatic418967fa.accept_10_7_5_2_1_880 27 115 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 115 162 (accept_3_5 26 115 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 115 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 115 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 115 162 (Polychromatic418967fa.accept_11_2_5_8_1_470 24 115 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 115 162 (accept_3_5 23 115 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 115 162 (Polychromatic418967fa.accept_15_7_10_12_1_2403 22 115
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 115 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 115 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 115 162 (accept_3_5 20 115 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 115 162 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 115 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 115 162 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 115 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 115 162 (accept_3_5 17 115 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 115 162 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 115 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 115 162
  (Polychromatic418967fa.accept_16_15_3_2_1_4170 15 115 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 115 162 (accept_3_5 14 115 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 115 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 115 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 115 162 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 115 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 115 162 (accept_3_5 11 115 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 115 162 (Polychromatic418967fa.accept_17_10_13_9_1_3913 10 115 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 115 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 115 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 115 162 (accept_3_5 8 115 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  115 162 (Polychromatic418967fa.accept_10_7_5_2_1_880 7 115 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 115 162 (Polychromatic418967fa.accept_15_6_10_12_1_2538 6 115 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 115 162 (accept_3_5 5 115 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 115 162 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 115 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 115 162
  (Polychromatic418967fa.accept_10_3_5_2_1_38 3 115 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 115 162 (accept_3_5 2 115 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  115 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 115 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 115 162)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 114 162 (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 114 162 6 8 19 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 114 162 (Polychromatic418967fa.accept_10_7_4_2_1_903 47 114 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 114 162 2 23 57 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 114 162 3 15 38 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 114 162 2 22 57 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 114 162
  (Polychromatic418967fa.accept_13_4_10_6_1_989 43 114 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 114 162 6 7 19 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 114 162 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 114 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 114 162 2 20 57 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 114 162 3 13 38 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 114 162 2 19 57 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 114 162
  (Polychromatic418967fa.accept_10_7_4_2_1_903 37 114 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 114 162 6 6 19 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 114 162 (Polychromatic418967fa.accept_13_9_10_6_1_1028 35 114 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 114 162 2 17 57 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 114 162 3 11 38 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 114 162 2 16 57 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 114 162
  (Polychromatic418967fa.accept_7_3_2_1_1_225 31 114 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 114 162 6 5 19 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 114 162 (Polychromatic418967fa.accept_11_7_4_8_1_1371 29 114 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 114 162 2 14 57 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 114 162 3 9 38 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 114 162 2 13 57 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 114 162
  (Polychromatic418967fa.accept_13_12_10_6_1_3212 25 114 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 114 162 6 4 19 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 114 162 (Polychromatic418967fa.accept_11_1_4_8_1_1918 23 114 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 114 162 2 11 57 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 114 162 3 7 38 54 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 114 162 2 10 57 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 114 162
  (Polychromatic418967fa.accept_15_4_9_12_1_2495 19 114 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 162 6 3 19 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 114 162 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 114 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 114 162 2 8 57 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 114 162 3 5 38 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 114 162 2 7 57 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 114 162 (Polychromatic418967fa.accept_7_6_2_1_1_214 13
  114 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 114 162 6 2 19 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 114 162
  (Polychromatic418967fa.accept_21_11_9_15_1_5746 11 114 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 114 162 2 5 57 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 9 114 162 3 3 38 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 8 114 162 2 4 57 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 7 114 162 (Polychromatic418967fa.accept_10_7_4_2_1_903 7 114 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114 162 6 1 19 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 114 162
  (Polychromatic418967fa.accept_13_5_10_6_1_2361 5 114 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 114 162 2 2 57 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 114 162 3 1 38 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 114 162 2 1 57 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 114 162 (Polychromatic418967fa.accept_11_1_4_8_1_1918 1 114 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 114 162))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 113
  162 (Eq.refl Bool.true) (allA_succ_of_accept 49 113 162 (accept_3_4 49 113 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 113 162 (Polychromatic418967fa.accept_15_3_8_12_1_900 48 113 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 113 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 113 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 113 162 (accept_3_4 46 113 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 113 162 (Polychromatic418967fa.accept_10_5_3_2_1_899 45 113 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 113 162 (Polychromatic418967fa.accept_14_2_1_8_1_650 44 113 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 113 162 (accept_3_4 43 113 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 113 162 (Polychromatic418967fa.accept_13_3_9_6_1_502 42 113
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 113 162
  (Polychromatic418967fa.accept_10_1_3_2_1_220 41 113 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 113 162 (accept_3_4 40 113 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 113 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 113 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 113 162 (Polychromatic418967fa.accept_11_5_3_8_1_454 38 113 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 113 162 (accept_3_4 37 113 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 113 162 (Polychromatic418967fa.accept_13_10_9_6_1_1026 36 113
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 113 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 113 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 113 162 (accept_3_4 34 113 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 113 162 (Polychromatic418967fa.accept_13_7_9_6_1_148 33 113 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 113 162 (Polychromatic418967fa.accept_25_7_13_12_1_9006 32 113 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 113 162 (accept_3_4 31 113 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 113 162 (Polychromatic418967fa.accept_13_4_9_6_1_2376 30 113
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 113 162
  (Polychromatic418967fa.accept_13_3_9_6_1_502 29 113 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 113 162 (accept_3_4 28 113 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 113 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 113 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 113 162 (Polychromatic418967fa.accept_15_11_8_12_1_4437 26 113 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 113 162 (accept_3_4 25 113 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 113 162 (Polychromatic418967fa.accept_19_5_18_10_1_4604 24 113
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 113 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 113 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 113 162 (accept_3_4 22 113 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 113 162 (Polychromatic418967fa.accept_10_1_3_2_1_220 21 113 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 113 162 (Polychromatic418967fa.accept_13_7_9_6_1_148 20 113 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 113 162 (accept_3_4 19 113 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 113 162 (Polychromatic418967fa.accept_15_3_8_12_1_900 18 113
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 113 162
  (Polychromatic418967fa.accept_11_6_3_8_1_843 17 113 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 113 162 (accept_3_4 16 113 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 113 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 113 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 113 162 (Polychromatic418967fa.accept_13_1_9_6_1_146 14 113 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 113 162 (accept_3_4 13 113 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 113 162 (Polychromatic418967fa.accept_16_12_1_2_1_2163 12 113
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 113 162
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 113 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 113 162 (accept_3_4 10 113 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  113 162 (Polychromatic418967fa.accept_14_9_1_8_1_2849 9 113 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 113 162 (Polychromatic418967fa.accept_17_8_11_9_1_5099 8 113 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 113 162 (accept_3_4 7 113 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 113 162 (Polychromatic418967fa.accept_11_6_3_8_1_843 6 113 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 113 162
  (Polychromatic418967fa.accept_10_5_3_2_1_899 5 113 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 113 162 (accept_3_4 4 113 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  113 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 113 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 113 162 (Polychromatic418967fa.accept_13_2_9_6_1_501 2 113 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 113 162 (accept_3_4 1 113 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 113 162)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 112 162
  (Eq.refl Bool.true) (allA_succ_of_gcd 50 112 162 2 25 56 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 112 162 (Polychromatic418967fa.accept_11_5_2_8_1_866 49 112 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 112 162 2 24 56 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 112 162 (accept_3_5 47
  112 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 112 162 2 23 56 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 112 162
  (Polychromatic418967fa.accept_12_9_4_6_1_460 45 112 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 112 162 2 22 56 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 112 162 (Polychromatic418967fa.accept_21_1_7_15_1_4259 43 112 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 112 162 2 21 56 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 112 162 (accept_3_5 41 112 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 112 162 2 20 56 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 112 162
  (Polychromatic418967fa.accept_12_3_4_6_1_434 39 112 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 112 162 2 19 56 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 112 162 (Polychromatic418967fa.accept_13_11_8_6_1_1023 37 112 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 112 162 2 18 56 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 112 162 (accept_3_5 35 112 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 112 162 2 17 56 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 112 162
  (Polychromatic418967fa.accept_12_9_4_6_1_460 33 112 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 112 162 2 16 56 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 112 162 (Polychromatic418967fa.accept_19_12_17_10_1_7365 31 112 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 112 162 2 15 56 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 112 162 (accept_3_5 29 112 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 112 162 2 14 56 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 112 162
  (Polychromatic418967fa.accept_11_5_2_8_1_866 27 112 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 112 162 2 13 56 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 112 162 (Polychromatic418967fa.accept_15_10_7_12_1_2490 25 112 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 112 162 2 12 56 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 112 162 (accept_3_5 23 112 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 112 162 2 11 56 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 112 162
  (Polychromatic418967fa.accept_12_9_4_6_1_460 21 112 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 112 162 2 10 56 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 112 162 (Polychromatic418967fa.accept_15_4_7_12_1_5538 19 112 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 112 162 2 9 56 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 112 162 (accept_3_5 17 112 162
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 112 162 2 8 56 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 112 162
  (Polychromatic418967fa.accept_12_3_4_6_1_434 15 112 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 112 162 2 7 56 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 112 162 (Polychromatic418967fa.accept_17_13_10_9_1_946 13 112 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 112 162 2 6 56 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 112 162 (accept_3_5 11 112 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 112 162 2 5 56 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 112 162 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 112 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 112 162 2 4 56 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 112 162
  (Polychromatic418967fa.accept_19_7_17_10_1_4630 7 112 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 112 162 2 3 56 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 112 162 (accept_3_5 5 112 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 112
  162 2 2 56 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  112 162 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 112 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 112 162 2 1 56 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 112 162 (Polychromatic418967fa.accept_13_1_8_6_1_1016 1 112 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112 162)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 52 111 162 (Eq.refl Bool.true) (allA_succ_of_gcd 51 111 162 3 17 37 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 111 162
  (Polychromatic418967fa.accept_12_2_3_6_1_112 50 111 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 111 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 111 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 111 162 3 16 37 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 111 162 (Polychromatic418967fa.accept_7_5_6_1_1_407 47
  111 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 111 162
  (Polychromatic418967fa.accept_10_6_1_2_1_874 46 111 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 111 162 3 15 37 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 111 162 (Polychromatic418967fa.accept_7_2_6_1_1_73 44 111 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 162 (Polychromatic418967fa.accept_10_3_1_2_1_521
  43 111 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 111 162 3 14 37 54
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 111 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 111 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 111 162 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 111 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 111 162 3 13 37 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 111 162 (Polychromatic418967fa.accept_12_2_3_6_1_112
  38 111 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 162
  (Polychromatic418967fa.accept_4_1_3_2_1_3 37 111 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 111 162 3 12 37 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 111 162 (Polychromatic418967fa.accept_13_9_7_6_1_1673 35 111 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 111 162
  (Polychromatic418967fa.accept_12_10_3_6_1_882 34 111 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 111 162 3 11 37 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 111 162 (Polychromatic418967fa.accept_12_8_3_6_1_909 32 111 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 162
  (Polychromatic418967fa.accept_21_10_6_15_1_8929 31 111 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 111 162 3 10 37 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 111 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 111 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 162
  (Polychromatic418967fa.accept_12_4_3_6_1_879 28 111 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 111 162 3 9 37 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 111 162 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 111 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 111 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 111 162 3 8 37 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 111 162
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 111 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 111 162 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 111 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 111 162 3 7 37 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 111 162 (Polychromatic418967fa.accept_12_8_3_6_1_909
  20 111 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 162
  (Polychromatic418967fa.accept_7_5_6_1_1_407 19 111 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 111 162 3 6 37 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 111 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 111 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 162 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 111 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 111 162 3 5 37 54 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 111 162
  (Polychromatic418967fa.accept_12_2_3_6_1_112 14 111 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 111 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 111 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 111 162 3 4 37 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 111 162
  (Polychromatic418967fa.accept_21_11_6_15_1_5764 11 111 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 111 162 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 111 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 111 162 3 3 37 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 111 162
  (Polychromatic418967fa.accept_12_8_3_6_1_909 8 111 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 111 162 (Polychromatic418967fa.accept_14_7_13_8_1_2067 7 111 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 111 162 3 2 37 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 111 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 111 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 162
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 4 111 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 111 162 3 1 37 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 111 162 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 111 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 111 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111
  162)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 110 162 (Eq.refl Bool.true) (allA_succ_of_gcd
  52 110 162 2 26 55 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 110 162 (Polychromatic418967fa.accept_12_3_2_6_1_138 51 110 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 110 162 2 25 55 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 110 162 (accept_3_4 49 110 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 110 162 2 24 55 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 110 162 (Polychromatic418967fa.accept_15_2_5_12_1_369 47 110
  162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 110 162 2 23 55 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 110 162
  (Polychromatic418967fa.accept_7_3_5_1_1_72 45 110 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 110 162 2 22 55 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 110 162 (accept_3_4 43 110 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 110 162 2 21 55 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 110 162 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 110 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 110 162 2 20 55 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 110 162
  (Polychromatic418967fa.accept_7_4_5_1_1_418 39 110 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 110 162 2 19 55 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 110 162 (accept_3_4 37 110 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 110 162 2 18 55 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 110 162 (Polychromatic418967fa.accept_17_1_8_9_1_1810 35 110 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 110 162 2 17 55 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 110 162
  (Polychromatic418967fa.accept_12_9_2_6_1_455 33 110 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 110 162 2 16 55 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 110 162 (accept_3_4 31 110 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 110 162 2 15 55 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 110 162 (Polychromatic418967fa.accept_21_8_5_15_1_4208 29 110 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 110 162 2 14 55 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 110 162
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 110 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 110 162 2 13 55 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 110 162 (accept_3_4 25 110 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 110 162 2 12 55 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 110 162 (Polychromatic418967fa.accept_15_8_5_12_1_4453 23 110 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 110 162 2 11 55 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 110 162
  (Polychromatic418967fa.accept_12_9_2_6_1_455 21 110 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 110 162 2 10 55 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 110 162 (accept_3_4 19 110 162 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 110 162 2 9 55 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 110 162 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 110 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 110 162 2 8 55 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 110 162 (Polychromatic418967fa.accept_12_3_2_6_1_138
  15 110 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 110 162 2 7 55 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 110 162
  (accept_3_4 13 110 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 110 162 2 6 55 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 110 162
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 110 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 110 162 2 5 55 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 110 162 (Polychromatic418967fa.accept_12_9_2_6_1_455 9 110 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 110 162 2 4 55 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 110 162 (accept_3_4 7 110 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 110 162 2 3 55 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 110 162 (Polychromatic418967fa.accept_19_5_15_10_1_7405 5 110 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 110 162 2 2 55 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 110 162
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 110 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 110 162 2 1 55 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 110 162 (accept_3_4 1 110 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  162))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 109 162 (Eq.refl Bool.true)
  (allA_succ_of_accept 53 109 162 (accept_3_5 53 109 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 109 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 109 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 109 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 109 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 109 162 (accept_3_5 50 109 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 109 162 (Polychromatic418967fa.accept_13_10_5_6_1_1671 49 109 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 109 162
  (Polychromatic418967fa.accept_21_6_4_15_1_9005 48 109 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 109 162 (accept_3_5 47 109 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 109 162 (Polychromatic418967fa.accept_14_4_11_8_1_2034 46 109 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 109 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 109 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 109 162 (accept_3_5 44 109 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 109 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 109 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 109 162
  (Polychromatic418967fa.accept_11_9_10_8_1_444 42 109 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 109 162 (accept_3_5 41 109 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 109 162 (Polychromatic418967fa.accept_7_5_4_1_1_412 40 109 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 109 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 109 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 109 162 (accept_3_5 38 109 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 109 162 (Polychromatic418967fa.accept_10_7_9_2_1_1887 37 109 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 109 162
  (Polychromatic418967fa.accept_13_10_5_6_1_1671 36 109 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 109 162 (accept_3_5 35 109 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 109 162 (Polychromatic418967fa.accept_19_15_14_10_1_4667 34 109 162 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 109 162 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 109 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 109 162 (accept_3_5 32 109 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 109 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 109 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 109 162
  (Polychromatic418967fa.accept_13_4_5_6_1_3201 30 109 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 109 162 (accept_3_5 29 109 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 109 162 (Polychromatic418967fa.accept_25_3_9_12_1_9004 28 109 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 109 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 109 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 109 162 (accept_3_5 26 109 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 109 162 (Polychromatic418967fa.accept_13_12_5_6_1_1050 25 109 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 109 162
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 109 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 109 162 (accept_3_5 23 109 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 109 162 (Polychromatic418967fa.accept_15_7_4_12_1_2530 22 109 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 109 162 (Polychromatic418967fa.accept_10_1_9_2_1_45 21 109 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 109 162 (accept_3_5 20 109 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 109 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 109 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 109 162
  (Polychromatic418967fa.accept_14_4_11_8_1_2034 18 109 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 109 162 (accept_3_5 17 109 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 109 162 (Polychromatic418967fa.accept_13_3_5_6_1_3192 16 109 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 109 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 109 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 109 162 (accept_3_5 14 109 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 109 162 (Polychromatic418967fa.accept_20_13_9_2_1_5933 13 109 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 109 162
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 109 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 109 162 (accept_3_5 11 109 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 109 162 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 109 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 109 162 (Polychromatic418967fa.accept_11_9_10_8_1_444 9 109 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 109 162 (accept_3_5 8 109 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 109 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 109 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 109 162
  (Polychromatic418967fa.accept_19_6_14_10_1_4624 6 109 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 109 162 (accept_3_5 5 109 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  109 162 (Polychromatic418967fa.accept_13_4_5_6_1_3201 4 109 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 109 162 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 109 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 109 162 (accept_3_5 2 109 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 109 162 (Polychromatic418967fa.accept_10_1_9_2_1_45 1 109 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 109
  162)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 108 162 (Eq.refl Bool.true) (allA_succ_of_gcd
  54 108 162 54 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 108 162 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 108 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 108 162 2 26 54 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 108 162 3 17 36 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 108 162 2 25 54 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 108 162
  (Polychromatic418967fa.accept_13_10_4_6_1_3224 49 108 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 108 162 6 8 18 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 108 162 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 108 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 108 162 2 23 54 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 108 162 9 5 12 18 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 108 162 2 22 54 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 108 162
  (Polychromatic418967fa.accept_11_10_9_8_1_1974 43 108 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 108 162 6 7 18 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 108 162 (Polychromatic418967fa.accept_13_2_4_6_1_2356 41 108 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 108 162 2 20 54 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 108 162 3 13 36 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 108 162 2 19 54 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 108 162
  (Polychromatic418967fa.accept_7_2_3_1_1_10 37 108 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 108 162 18 2 6 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 108 162 (Polychromatic418967fa.accept_10_5_8_2_1_517 35 108 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 108 162 2 17 54 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 108 162 3 11 36 54 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 108 162 2 16 54 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 108 162
  (Polychromatic418967fa.accept_13_5_4_6_1_2371 31 108 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 108 162 6 5 18 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 108 162 (Polychromatic418967fa.accept_21_8_3_15_1_2875 29 108 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 108 162 2 14 54 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 108 162 27 1 4 6 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 108 162 2 13 54 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 108 162
  (Polychromatic418967fa.accept_7_4_3_1_1_87 25 108 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 108 162 6 4 18 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 108 162 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 108 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 108 162 2 11 54 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 108 162 3 7 36 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 108 162 2 10 54 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 108 162
  (Polychromatic418967fa.accept_7_5_3_1_1_424 19 108 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 108 162 18 1 6 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 108 162 (Polychromatic418967fa.accept_15_2_3_12_1_891 17 108 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 108 162 2 8 54 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 108 162 3 5 36 54 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 108 162 2 7 54 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 108 162
  (Polychromatic418967fa.accept_15_13_3_12_1_1609 13 108 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 108 162 6 2 18 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 108 162 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 108 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 108 162 2 5 54 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 108 162 9 1 12 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 108 162 2 4 54 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 108 162
  (Polychromatic418967fa.accept_13_7_4_6_1_3221 7 108 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 108 162 6 1 18 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 108 162 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 108 162 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 108 162 2 2 54 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 108 162 3 1 36 54 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 108 162 2 1 54 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 108 162 (Polychromatic418967fa.accept_16_1_12_2_1_2136 1 108 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  162))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 107 162 (Eq.refl Bool.true)
  (allA_succ_of_accept 55 107 162 (accept_3_4 55 107 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 107 162 (Polychromatic418967fa.accept_10_4_7_2_1_211 54 107 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 107 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 107 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 107 162 (accept_3_4 52 107 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 107 162 (Polychromatic418967fa.accept_15_6_2_12_1_885 51 107 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 107 162
  (Polychromatic418967fa.accept_15_5_2_12_1_2543 50 107 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 107 162 (accept_3_4 49 107 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 107 162 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 107 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 107 162 (Polychromatic418967fa.accept_17_13_5_9_1_1762 47 107 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 107 162 (accept_3_4 46 107 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 107 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 107 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 107 162
  (Polychromatic418967fa.accept_10_4_7_2_1_211 44 107 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 107 162 (accept_3_4 43 107 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 107 162 (Polychromatic418967fa.accept_22_20_19_8_1_9003 42 107 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 107 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 107 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 107 162 (accept_3_4 40 107 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 107 162 (Polychromatic418967fa.accept_10_9_7_2_1_887 39 107 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 107 162
  (Polychromatic418967fa.accept_7_3_2_1_1_225 38 107 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 107 162 (accept_3_4 37 107 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 107 162 (Polychromatic418967fa.accept_13_10_3_6_1_1003 36 107 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 107 162 (Polychromatic418967fa.accept_10_5_7_2_1_516 35 107 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 107 162 (accept_3_4 34 107 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 107 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 107 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 107 162
  (Polychromatic418967fa.accept_20_12_7_2_1_4448 32 107 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 107 162 (accept_3_4 31 107 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 107 162 (Polychromatic418967fa.accept_17_13_5_9_1_1762 30 107 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 107 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 107 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 107 162 (accept_3_4 28 107 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 107 162 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 107 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 107 162
  (Polychromatic418967fa.accept_24_2_11_18_1_131 26 107 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 107 162 (accept_3_4 25 107 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 107 162 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 107 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 107 162 (Polychromatic418967fa.accept_13_10_3_6_1_1003 23 107 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 107 162 (accept_3_4 22 107 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 107 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 107 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 107 162
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 107 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 107 162 (accept_3_4 19 107 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 107 162 (Polychromatic418967fa.accept_13_5_3_6_1_3278 18 107 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 107 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 107 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 107 162 (accept_3_4 16 107 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 107 162 (Polychromatic418967fa.accept_10_5_7_2_1_516 15 107 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 162
  (Polychromatic418967fa.accept_10_4_7_2_1_211 14 107 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 107 162 (accept_3_4 13 107 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 107 162 (Polychromatic418967fa.accept_17_12_5_9_1_6372 12 107 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 107 162 (Polychromatic418967fa.accept_19_11_12_10_1_7480 11 107 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 162 (accept_3_4 10 107 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 107 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 107 162
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 162
  (Polychromatic418967fa.accept_19_8_12_10_1_9002 8 107 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 107 162 (accept_3_4 7 107 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  107 162 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 107 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 107 162 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 107 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 162 (accept_3_4 4 107 162 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 162 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 107 162 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 162
  (Polychromatic418967fa.accept_19_2_12_10_1_7478 2 107 162 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 107 162 (accept_3_4 1 107 162 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107
  162))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_162_segment_000)))))))))))))))))))))))))))))))))))))))))))))))))))))))


