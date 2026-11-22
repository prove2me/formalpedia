-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch133
-- name    : Polychromatic418967fa_Branch133
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:13:43.969048+00:00
-- url     : https://prove2.me/theorems/b376d5d5-e6c5-4ac3-879e-614800fd1b65
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

def Polychromatic418967fa.branch_133 : allB 133 133 :=
  allB_succ' 2 132 133 (Eq.refl Bool.true) (allA_succ_of_accept 1 132 133 (Polychromatic418967fa.accept_8_1_4_5_1_48 1
  132 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132 133)) (allB_succ' 3 131 133
  (Eq.refl Bool.true) (allA_of_3_1 3 131 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 130 133 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 130 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 130 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 130 133 (accept_3_3 2 130 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 130 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 130 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 130 133)))) (allB_succ' 5 129 133 (Eq.refl Bool.true)
  (allA_succ_of_accept 4 129 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 129 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 129 133 (Polychromatic418967fa.accept_12_3_9_1_1_290 3 129 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 129 133 (accept_3_3 2 129 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 133 (Polychromatic418967fa.accept_9_1_3_7_1_6 1
  129 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129 133))))) (allB_succ' 6 128 133
  (Eq.refl Bool.true) (allA_of_3_1 6 128 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 127 133 (Eq.refl
  Bool.true) (allA_succ_of_accept 6 127 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 127 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 127 133 (accept_3_3 5 127 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 127 133 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 127 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 127 133
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 127 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 127 133 (accept_3_3 2 127 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  127 133 (Polychromatic418967fa.accept_16_1_15_5_1_708 1 127 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 127 133))))))) (allB_succ' 8 126 133 (Eq.refl Bool.true) (allA_succ_of_gcd 7 126 133 7 1 18 19
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 126 133
  (Polychromatic418967fa.accept_11_6_5_1_1_586 6 126 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 126 133 (accept_3_3 5 126 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  126 133 (Polychromatic418967fa.accept_15_4_6_13_1_956 4 126 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 126 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 126 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 126 133 (accept_3_3 2 126 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 126 133 (Polychromatic418967fa.accept_27_1_18_25_1_6791 1 126 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126 133)))))))) (allB_succ' 9 125 133 (Eq.refl
  Bool.true) (allA_of_3_1 9 125 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 124 133 (Eq.refl Bool.true)
  (allA_succ_of_accept 9 124 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 124 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 124 133 (accept_3_3 8 124 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 124 133 (Polychromatic418967fa.accept_10_7_4_3_1_560 7 124 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 124 133 (Polychromatic418967fa.accept_15_6_4_13_1_403
  6 124 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 124 133 (accept_3_3 5
  124 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 124 133
  (Polychromatic418967fa.accept_13_4_7_3_1_92 4 124 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 124 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 124 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 124 133 (accept_3_3 2 124 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 124 133 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 124 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 124 133)))))))))) (allB_succ' 11 123 133 (Eq.refl Bool.true)
  (allA_succ_of_accept 10 123 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 123 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 123 133 (Polychromatic418967fa.accept_12_9_3_1_1_303 9 123 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 123 133 (accept_3_3 8 123 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 133 (Polychromatic418967fa.accept_16_7_11_5_1_4402
  7 123 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 133
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 123 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 123 133 (accept_3_3 5 123 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  123 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 123 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 123 133 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 123 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 123 133 (accept_3_3 2 123 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 133 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 123 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 123 133))))))))))) (allB_succ' 12 122 133 (Eq.refl
  Bool.true) (allA_of_3_1 12 122 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 121 133 (Eq.refl Bool.true)
  (allA_succ_of_accept 12 121 133 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 121 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 121 133 (accept_3_3 11 121 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 121 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 121 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 121 133 (Polychromatic418967fa.accept_21_9_16_7_1_5222
  9 121 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 121 133 (accept_3_3 8
  121 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 121 133
  (Polychromatic418967fa.accept_13_7_4_3_1_3064 7 121 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 121 133 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 121 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 121 133 (accept_3_3 5 121 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 121 133 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 121 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 121 133 (Polychromatic418967fa.accept_9_3_4_7_1_89 3
  121 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 121 133 (accept_3_3 2 121
  133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 121 133 (Polychromatic418967fa.accept_9_1_4_7_1_7
  1 121 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 121 133))))))))))))) (allB_succ' 14
  120 133 (Eq.refl Bool.true) (allA_succ_of_accept 13 120 133 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 120 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 120 133
  (Polychromatic418967fa.accept_16_12_8_5_1_3316 12 120 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 120 133 (accept_3_3 11 120 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 120 133 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 120 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 120 133 (Polychromatic418967fa.accept_11_9_10_1_1_581 9 120 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 120 133 (accept_3_3 8 120 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 120 133 (Polychromatic418967fa.accept_23_7_5_18_1_6772 7 120 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 120 133
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 120 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 120 133 (accept_3_3 5 120 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  120 133 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 120 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 120 133 (Polychromatic418967fa.accept_16_3_8_5_1_6790 3 120 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 120 133 (accept_3_3 2 120 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 120 133 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 120 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120 133)))))))))))))) (allB_succ' 15 119 133 (Eq.refl
  Bool.true) (allA_of_3_1 15 119 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 118 133 (Eq.refl Bool.true)
  (allA_succ_of_accept 15 118 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 118 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 118 133 (accept_3_3 14 118 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 118 133 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 118 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 118 133 (Polychromatic418967fa.accept_9_3_1_7_1_97 12
  118 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 118 133 (accept_3_3 11
  118 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 118 133
  (Polychromatic418967fa.accept_21_10_13_7_1_6789 10 118 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 118 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 118 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 118 133 (accept_3_3 8 118 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 118 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 118 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 118 133
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 118 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 118 133 (accept_3_3 5 118 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  118 133 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 118 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 118 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 118 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 118 133 (accept_3_3 2 118 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 118 133 (Polychromatic418967fa.accept_10_1_8_3_1_947 1 118 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118 133)))))))))))))))) (allB_succ' 17 117 133 (Eq.refl
  Bool.true) (allA_succ_of_accept 16 117 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 117 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 117 133 (Polychromatic418967fa.accept_10_5_7_3_1_561
  15 117 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 133 (accept_3_3 14
  117 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 133
  (Polychromatic418967fa.accept_23_13_2_18_1_6788 13 117 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 117 133 (Polychromatic418967fa.accept_14_12_5_7_1_2010 12 117 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 117 133 (accept_3_3 11 117 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 117 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 133
  (Polychromatic418967fa.accept_14_9_5_7_1_1251 9 117 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 117 133 (accept_3_3 8 117 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  117 133 (Polychromatic418967fa.accept_23_7_2_18_1_6787 7 117 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 117 133 (Polychromatic418967fa.accept_10_6_7_3_1_547 6 117 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 117 133 (accept_3_3 5 117 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 117 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 117 133
  (Polychromatic418967fa.accept_12_3_9_1_1_290 3 117 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 117 133 (accept_3_3 2 117 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  117 133 (Polychromatic418967fa.accept_15_1_12_13_1_944 1 117 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 117 133))))))))))))))))) (allB_succ' 18 116 133 (Eq.refl Bool.true) (allA_of_3_1 18 116 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 115 133 (Eq.refl Bool.true) (allA_succ_of_accept 18 115 133
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 115 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 115 133 (accept_3_3 17 115 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 115 133 (Polychromatic418967fa.accept_15_1_10_13_1_939 16 115 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 115 133 (Polychromatic418967fa.accept_13_2_11_3_1_873 15 115 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 115 133 (accept_3_3 14 115 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 115 133 (Polychromatic418967fa.accept_21_13_10_7_1_3701 13 115
  133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 115 133
  (Polychromatic418967fa.accept_10_2_5_3_1_1408 12 115 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 115 133 (accept_3_3 11 115 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 115 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 115 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 115 133 (Polychromatic418967fa.accept_21_9_10_7_1_383 9 115 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 115 133 (accept_3_3 8 115 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 115 133 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 115 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 115 133
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 115 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 115 133 (accept_3_3 5 115 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  115 133 (Polychromatic418967fa.accept_14_4_3_7_1_3702 4 115 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 115 133 (Polychromatic418967fa.accept_15_3_10_13_1_2605 3 115 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 133 (accept_3_3 2 115 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 115 133 (Polychromatic418967fa.accept_13_1_11_3_1_901 1 115 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115 133))))))))))))))))))) (allB_succ' 20 114
  133 (Eq.refl Bool.true) (allA_succ_of_gcd 19 114 133 19 1 6 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 18 114 133 (Polychromatic418967fa.accept_15_3_9_13_1_1681 18 114
  133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 114 133 (accept_3_3 17 114
  133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 114 133
  (Polychromatic418967fa.accept_21_16_9_7_1_6709 16 114 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 114 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 114 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 114 133 (accept_3_3 14 114 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 114 133 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 114 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 114 133 (Polychromatic418967fa.accept_9_3_6_7_1_562
  12 114 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 114 133 (accept_3_3 11
  114 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 114 133
  (Polychromatic418967fa.accept_9_1_6_7_1_285 10 114 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 114 133 (Polychromatic418967fa.accept_10_9_4_3_1_539 9 114 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 114 133 (accept_3_3 8 114 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 114 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 114 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 114 133 (Polychromatic418967fa.accept_13_6_10_3_1_897
  6 114 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 114 133 (accept_3_3 5
  114 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 114 133
  (Polychromatic418967fa.accept_9_4_6_7_1_286 4 114 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 114 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 114 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 114 133 (accept_3_3 2 114 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 114 133 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 114 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114 133)))))))))))))))))))) (allB_succ' 21 113 133 (Eq.refl
  Bool.true) (allA_of_3_1 21 113 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 112 133 (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 112 133 7 3 16 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 112 133 (accept_3_3 20 112 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 112 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 112 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 112 133 (Polychromatic418967fa.accept_13_5_8_3_1_1535 18 112 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 112 133 (accept_3_3 17 112 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 112 133 (Polychromatic418967fa.accept_18_16_4_7_1_2927 16 112
  133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 112 133
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 112 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 112 133 7 2 16 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 112 133 (Polychromatic418967fa.accept_17_13_10_14_1_4211 13 112 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 112 133 (Polychromatic418967fa.accept_9_3_4_7_1_89 12
  112 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 112 133 (accept_3_3 11
  112 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 112 133
  (Polychromatic418967fa.accept_9_1_4_7_1_7 10 112 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 112 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 112 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 112 133 (accept_3_3 8 112 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 7 112 133 7 1 16 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 6 112 133 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 112 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 112 133 (accept_3_3 5 112 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 112 133 (Polychromatic418967fa.accept_25_4_12_8_1_6786 4 112 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 112 133
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 112 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 112 133 (accept_3_3 2 112 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  112 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 112 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 112 133)))))))))))))))))))))) (allB_succ' 23 111 133 (Eq.refl Bool.true) (allA_succ_of_accept 22
  111 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 111 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 111 133 (Polychromatic418967fa.accept_12_9_3_1_1_303 21 111 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 111 133 (accept_3_3 20 111 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 133 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 111 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 133
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 111 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 111 133 (accept_3_3 17 111 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 111 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 111 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 111 133 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 111 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 111 133 (accept_3_3 14 111 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 133 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 111 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 133
  (Polychromatic418967fa.accept_10_2_1_3_1_233 12 111 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 111 133 (accept_3_3 11 111 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 111 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 111 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 111 133 (Polychromatic418967fa.accept_12_9_3_1_1_303 9 111 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 133 (accept_3_3 8 111 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 133 (Polychromatic418967fa.accept_15_7_6_13_1_936 7 111 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 133
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 111 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 111 133 (accept_3_3 5 111 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  111 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 111 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 111 133 (Polychromatic418967fa.accept_20_3_11_13_1_6785 3 111 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 133 (accept_3_3 2 111 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 133 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 111 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111 133))))))))))))))))))))))) (allB_succ' 24
  110 133 (Eq.refl Bool.true) (allA_of_3_1 24 110 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 109 133
  (Eq.refl Bool.true) (allA_succ_of_accept 24 109 133 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 109 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 109 133 (accept_3_3 23 109 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 109 133 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 109 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 109 133
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 109 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 109 133 (accept_3_3 20 109 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 109 133 (Polychromatic418967fa.accept_13_6_5_3_1_426 19 109 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 109 133 (Polychromatic418967fa.accept_14_4_11_7_1_1234 18 109 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 109 133 (accept_3_3 17 109 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 109 133 (Polychromatic418967fa.accept_10_6_9_3_1_935 16 109
  133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 109 133
  (Polychromatic418967fa.accept_9_6_1_7_1_577 15 109 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 109 133 (accept_3_3 14 109 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 109 133 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 109 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 109 133 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 109 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 109 133 (accept_3_3 11 109 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 109 133 (Polychromatic418967fa.accept_14_10_11_7_1_1955 10 109 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 109 133
  (Polychromatic418967fa.accept_11_9_10_1_1_581 9 109 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 109 133 (accept_3_3 8 109 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  109 133 (Polychromatic418967fa.accept_25_7_9_8_1_6784 7 109 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 109 133 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 109 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 109 133 (accept_3_3 5 109 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 109 133 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 109 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 109 133
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 109 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 109 133 (accept_3_3 2 109 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  109 133 (Polychromatic418967fa.accept_13_1_5_3_1_888 1 109 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 109 133))))))))))))))))))))))))) (allB_succ' 26 108 133 (Eq.refl Bool.true) (allA_succ_of_accept
  25 108 133 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 108 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 108 133 (Polychromatic418967fa.accept_15_9_3_13_1_1686 24 108 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 108 133 (accept_3_3 23 108 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 108 133 (Polychromatic418967fa.accept_21_1_3_7_1_3727 22 108
  133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 108 133
  (Polychromatic418967fa.accept_10_1_8_3_1_947 21 108 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 108 133 (accept_3_3 20 108 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 108 133 (Polychromatic418967fa.accept_22_19_20_1_1_6783 19 108 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 108 133 (Polychromatic418967fa.accept_14_4_10_7_1_1946 18 108 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 108 133 (accept_3_3 17 108 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 108 133 (Polychromatic418967fa.accept_10_6_8_3_1_930 16 108
  133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 108 133
  (Polychromatic418967fa.accept_10_5_8_3_1_229 15 108 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 108 133 (accept_3_3 14 108 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 108 133 (Polychromatic418967fa.accept_23_13_16_18_1_6782 13 108 133 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 108 133 (Polychromatic418967fa.accept_13_12_4_3_1_1528 12 108 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 108 133 (accept_3_3 11 108 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 108 133
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 10 108 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 108 133 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 108 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 108 133 (accept_3_3 8 108 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 108 133 (Polychromatic418967fa.accept_13_7_4_3_1_3064 7 108 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 108 133 (Polychromatic418967fa.accept_10_6_8_3_1_930 6
  108 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 108 133 (accept_3_3 5 108
  133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 108 133
  (Polychromatic418967fa.accept_14_4_10_7_1_1946 4 108 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 108 133 (Polychromatic418967fa.accept_14_3_10_7_1_3773 3 108 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 108 133 (accept_3_3 2 108 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 108 133 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 108 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108 133)))))))))))))))))))))))))) (allB_succ' 27 107 133 (Eq.refl
  Bool.true) (allA_of_3_1 27 107 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 106 133 (Eq.refl Bool.true)
  (allA_succ_of_accept 27 106 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 106 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 106 133 (accept_3_3 26 106 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 106 133 (Polychromatic418967fa.accept_13_12_2_3_1_1527 25 106 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 106 133
  (Polychromatic418967fa.accept_13_11_2_3_1_883 24 106 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 106 133 (accept_3_3 23 106 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 106 133 (Polychromatic418967fa.accept_13_9_2_3_1_3027 22 106 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 106 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 106 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 106 133 (accept_3_3 20 106 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 106 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 106 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 106 133
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 106 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 106 133 (accept_3_3 17 106 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 106 133 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 106 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 106 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 106 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 106 133 (accept_3_3 14 106 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 106 133 (Polychromatic418967fa.accept_14_13_8_7_1_1224 13 106 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 106 133
  (Polychromatic418967fa.accept_13_12_2_3_1_1527 12 106 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 106 133 (accept_3_3 11 106 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 106 133 (Polychromatic418967fa.accept_13_10_2_3_1_3025 10 106 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 106 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 106 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 106 133 (accept_3_3 8 106 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 106 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 106 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 106 133
  (Polychromatic418967fa.accept_11_6_7_1_1_564 6 106 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 106 133 (accept_3_3 5 106 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  106 133 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 106 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 106 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 106 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 106 133 (accept_3_3 2 106 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 106 133 (Polychromatic418967fa.accept_13_1_2_3_1_911 1 106 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106 133)))))))))))))))))))))))))))) (allB_succ' 29 105
  133 (Eq.refl Bool.true) (allA_succ_of_gcd 28 105 133 7 4 15 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 105 133 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 105 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 133 (accept_3_3 26 105 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 133
  (Polychromatic418967fa.accept_23_2_13_18_1_6781 25 105 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 105 133 (Polychromatic418967fa.accept_13_11_1_3_1_910 24 105 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 105 133 (accept_3_3 23 105 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 105 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 105 133 7 3 15 19 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 105 133 (accept_3_3 20
  105 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 133
  (Polychromatic418967fa.accept_9_1_6_7_1_285 19 105 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 105 133 (Polychromatic418967fa.accept_10_8_5_3_1_543 18 105 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 133 (accept_3_3 17 105 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 105 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 105 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 105 133 (Polychromatic418967fa.accept_12_3_9_1_1_290
  15 105 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 105 133 7 2 15 19
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 105 133
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 105 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 105 133 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 105 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 133 (accept_3_3 11 105 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 105 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 105 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 105 133
  (Polychromatic418967fa.accept_27_9_24_25_1_6780 9 105 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 105 133 (accept_3_3 8 105 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 105
  133 7 1 15 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6
  105 133 (Polychromatic418967fa.accept_13_6_1_3_1_1522 6 105 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 105 133 (accept_3_3 5 105 133 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 105 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 105 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 133 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 105 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 133 (accept_3_3 2 105 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 133 (Polychromatic418967fa.accept_9_1_6_7_1_285 1
  105 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105 133)))))))))))))))))))))))))))))
  (allB_succ' 30 104 133 (Eq.refl Bool.true) (allA_of_3_1 30 104 133 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 31 103 133 (Eq.refl Bool.true) (allA_succ_of_accept 30 103 133 (Polychromatic418967fa.accept_4_2_3_1_1_2
  30 103 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 103 133 (accept_3_3 29
  103 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 103 133
  (Polychromatic418967fa.accept_9_1_4_7_1_7 28 103 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 103 133 (Polychromatic418967fa.accept_16_11_7_5_1_4364 27 103 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 103 133 (accept_3_3 26 103 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 103 133 (Polychromatic418967fa.accept_21_4_19_7_1_5142 25 103 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 103 133
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 103 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 103 133 (accept_3_3 23 103 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 103 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 103 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 103 133 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 103 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 103 133 (accept_3_3 20 103 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 103 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 103 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 103 133
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 103 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 103 133 (accept_3_3 17 103 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 103 133 (Polychromatic418967fa.accept_14_2_5_7_1_3767 16 103 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 103 133 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 103 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 103 133 (accept_3_3 14 103 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 103 133 (Polychromatic418967fa.accept_17_13_1_14_1_1149 13 103 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 103 133
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 103 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 103 133 (accept_3_3 11 103 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 103 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 103 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 103 133 (Polychromatic418967fa.accept_13_9_12_3_1_907 9 103 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 103 133 (accept_3_3 8 103 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 103 133 (Polychromatic418967fa.accept_23_7_11_18_1_6779 7 103 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 103 133
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 103 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 103 133 (accept_3_3 5 103 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  103 133 (Polychromatic418967fa.accept_13_4_12_3_1_2999 4 103 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 103 133 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 103 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 103 133 (accept_3_3 2 103 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 103 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 103 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 103 133))))))))))))))))))))))))))))))) (allB_succ' 32
  102 133 (Eq.refl Bool.true) (allA_succ_of_accept 31 102 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 102 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 102 133
  (Polychromatic418967fa.accept_20_10_2_13_1_2560 30 102 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 102 133 (accept_3_3 29 102 133 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 102 133 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 102 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 102 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 102 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 102 133 (accept_3_3 26 102 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 102 133 (Polychromatic418967fa.accept_10_5_2_3_1_239
  25 102 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 102 133
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 102 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 102 133 (accept_3_3 23 102 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 102 133 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 102 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 102 133 (Polychromatic418967fa.accept_10_1_2_3_1_1910 21 102 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 102 133 (accept_3_3 20 102 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 102 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 102 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 102 133
  (Polychromatic418967fa.accept_13_5_11_3_1_902 18 102 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 102 133 (accept_3_3 17 102 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 102 133 (Polychromatic418967fa.accept_15_1_12_13_1_944 16 102 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 102 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 102 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 102 133 (accept_3_3 14 102 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 102 133 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 102 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 102 133
  (Polychromatic418967fa.accept_21_12_18_7_1_6740 12 102 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 102 133 (accept_3_3 11 102 133 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 102 133 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 102 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 102 133 (Polychromatic418967fa.accept_20_9_2_13_1_6778 9 102
  133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 102 133 (accept_3_3 8 102 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 102 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 7
  102 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 102 133
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 102 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 102 133 (accept_3_3 5 102 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  102 133 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 102 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 102 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 102 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 102 133 (accept_3_3 2 102 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 102 133 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 102 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102 133)))))))))))))))))))))))))))))))) (allB_succ' 33
  101 133 (Eq.refl Bool.true) (allA_of_3_1 33 101 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 100 133
  (Eq.refl Bool.true) (allA_succ_of_accept 33 100 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 100 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 100 133 (accept_3_3 32 100 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 100 133 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 100 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 100 133
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 100 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 100 133 (accept_3_3 29 100 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 100 133 (Polychromatic418967fa.accept_13_2_9_3_1_2212 28 100 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 100 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 100 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 100 133 (accept_3_3 26 100 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 100 133 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 100 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 100 133
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 100 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 100 133 (accept_3_3 23 100 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 100 133 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 100 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 100 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 100 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 100 133 (accept_3_3 20 100 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 100 133 (Polychromatic418967fa.accept_13_6_9_3_1_915 19 100 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 100 133
  (Polychromatic418967fa.accept_13_5_9_3_1_870 18 100 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 100 133 (accept_3_3 17 100 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 100 133 (Polychromatic418967fa.accept_15_1_10_13_1_939 16 100 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 100 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 100 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 100 133 (accept_3_3 14 100 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 100 133 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 100 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 100 133
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 100 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 100 133 (accept_3_3 11 100 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 100 133 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 100 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 100 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 100 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 100 133 (accept_3_3 8 100 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 100 133 (Polychromatic418967fa.accept_13_7_9_3_1_1504 7 100 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 100 133
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 100 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 100 133 (accept_3_3 5 100 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  100 133 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 100 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 100 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 100 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 100 133 (accept_3_3 2 100 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 100 133 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 100 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 100 133)))))))))))))))))))))))))))))))))) (allB_succ' 35
  99 133 (Eq.refl Bool.true) (allA_succ_of_accept 34 99 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 99 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 133
  (Polychromatic418967fa.accept_12_9_3_1_1_303 33 99 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 99 133 (accept_3_3 32 99 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  99 133 (Polychromatic418967fa.accept_13_5_8_3_1_1535 31 99 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 99 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 99 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 133 (accept_3_3 29 99 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 99 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 133
  (Polychromatic418967fa.accept_14_13_1_7_1_1211 27 99 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 99 133 (accept_3_3 26 99 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  99 133 (Polychromatic418967fa.accept_20_5_19_13_1_6717 25 99 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 99 133 (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 99 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 99 133 (accept_3_3 23 99 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 99 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 133
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 99 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 99 133 (accept_3_3 20 99 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  99 133 (Polychromatic418967fa.accept_15_4_9_13_1_2582 19 99 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 99 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 99 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 133 (accept_3_3 17 99 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 99 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 133
  (Polychromatic418967fa.accept_22_15_11_1_1_6777 15 99 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 99 133 (accept_3_3 14 99 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  99 133 (Polychromatic418967fa.accept_14_13_1_7_1_1211 13 99 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 99 133 (Polychromatic418967fa.accept_20_12_19_13_1_6776 12 99 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 99 133 (accept_3_3 11 99 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 99 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 133
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 99 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 99 133 (accept_3_3 8 99 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99
  133 (Polychromatic418967fa.accept_13_7_8_3_1_1533 7 99 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 99 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 99 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 133 (accept_3_3 5 99 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 99 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99 133
  (Polychromatic418967fa.accept_15_3_9_13_1_1681 3 99 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 99 133 (accept_3_3 2 99 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99
  133 (Polychromatic418967fa.accept_21_1_15_7_1_6775 1 99 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 99 133))))))))))))))))))))))))))))))))))) (allB_succ' 36 98 133 (Eq.refl Bool.true) (allA_of_3_1
  36 98 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 97 133 (Eq.refl Bool.true) (allA_succ_of_accept 36
  97 133 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 97 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 97 133 (accept_3_3 35 97 133 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 97 133 (Polychromatic418967fa.accept_10_4_7_3_1_54 34 97 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 97 133 (Polychromatic418967fa.accept_23_10_5_18_1_6774 33 97
  133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 97 133 (accept_3_3 32 97 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 97 133 (Polychromatic418967fa.accept_13_5_6_3_1_868
  31 97 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 97 133
  (Polychromatic418967fa.accept_20_10_17_13_1_6773 30 97 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 97 133 (accept_3_3 29 97 133 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 97 133 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 97 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 97 133 (Polychromatic418967fa.accept_13_1_6_3_1_1547 27 97 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 97 133 (accept_3_3 26 97 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 97 133 (Polychromatic418967fa.accept_10_5_7_3_1_561
  25 97 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 97 133
  (Polychromatic418967fa.accept_10_4_7_3_1_54 24 97 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 97 133 (accept_3_3 23 97 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  97 133 (Polychromatic418967fa.accept_13_9_6_3_1_1514 22 97 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 97 133 (Polychromatic418967fa.accept_11_10_9_1_1_2186 21 97 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 97 133 (accept_3_3 20 97 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 97 133 (Polychromatic418967fa.accept_21_19_13_7_1_3706 19 97
  133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 97 133
  (Polychromatic418967fa.accept_13_5_6_3_1_868 18 97 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 97 133 (accept_3_3 17 97 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  97 133 (Polychromatic418967fa.accept_10_6_7_3_1_547 16 97 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 97 133 (Polychromatic418967fa.accept_10_5_7_3_1_561 15 97 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 97 133 (accept_3_3 14 97 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 97 133 (Polychromatic418967fa.accept_16_13_1_5_1_5469 13 97 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 97 133
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 97 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 97 133 (accept_3_3 11 97 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  97 133 (Polychromatic418967fa.accept_11_10_9_1_1_2186 10 97 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 97 133 (Polychromatic418967fa.accept_13_9_6_3_1_1514 9 97 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 133 (accept_3_3 8 97 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 97 133 (Polychromatic418967fa.accept_23_7_5_18_1_6772 7 97 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 133
  (Polychromatic418967fa.accept_10_6_7_3_1_547 6 97 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 97 133 (accept_3_3 5 97 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97
  133 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 97 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 97 133 (Polychromatic418967fa.accept_22_3_9_1_1_6771 3 97 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 133 (accept_3_3 2 97 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 97 133 (Polychromatic418967fa.accept_13_1_6_3_1_1547 1 97 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97 133))))))))))))))))))))))))))))))))))))) (allB_succ' 38 96 133
  (Eq.refl Bool.true) (allA_succ_of_accept 37 96 133 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 96 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 96 133
  (Polychromatic418967fa.accept_21_15_12_7_1_5204 36 96 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 96 133 (accept_3_3 35 96 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  96 133 (Polychromatic418967fa.accept_13_8_5_3_1_427 34 96 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 96 133 (Polychromatic418967fa.accept_14_5_12_7_1_2767 33 96 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 96 133 (accept_3_3 32 96 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 96 133 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 96 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 96 133
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 96 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 96 133 (accept_3_3 29 96 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  96 133 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 96 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 96 133 (Polychromatic418967fa.accept_10_7_6_3_1_927 27 96 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 96 133 (accept_3_3 26 96 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 96 133 (Polychromatic418967fa.accept_17_8_11_14_1_6770 25 96 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 96 133
  (Polychromatic418967fa.accept_13_11_5_3_1_889 24 96 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 96 133 (accept_3_3 23 96 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  96 133 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 96 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 96 133 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 96 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 96 133 (accept_3_3 20 96 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 133 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 96 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 96 133
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 96 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 96 133 (accept_3_3 17 96 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  96 133 (Polychromatic418967fa.accept_14_2_12_7_1_617 16 96 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 96 133 (Polychromatic418967fa.accept_11_4_8_1_1_1047 15 96 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 96 133 (accept_3_3 14 96 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 133 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 96 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 96 133
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 96 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 96 133 (accept_3_3 11 96 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  96 133 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 96 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 96 133 (Polychromatic418967fa.accept_10_9_6_3_1_545 9 96 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 96 133 (accept_3_3 8 96 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 133 (Polychromatic418967fa.accept_10_7_6_3_1_927 7 96 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 96 133
  (Polychromatic418967fa.accept_13_6_5_3_1_426 6 96 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 96 133 (accept_3_3 5 96 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 96
  133 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 96 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 96 133 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 96 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 96 133 (accept_3_3 2 96 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 96 133 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 96 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96 133)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 95 133
  (Eq.refl Bool.true) (allA_of_3_1 39 95 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 40 94 133 (Eq.refl
  Bool.true) (allA_succ_of_accept 39 94 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 94 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 94 133 (accept_3_3 38 94 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 94 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 94 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 94 133
  (Polychromatic418967fa.accept_15_6_4_13_1_403 36 94 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 94 133 (accept_3_3 35 94 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  94 133 (Polychromatic418967fa.accept_18_16_4_7_1_2927 34 94 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 94 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 94 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 94 133 (accept_3_3 32 94 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 94 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 94 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 94 133
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 94 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 94 133 (accept_3_3 29 94 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  94 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 94 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 94 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 94 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 94 133 (accept_3_3 26 94 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 94 133 (Polychromatic418967fa.accept_14_11_10_7_1_1948 25 94 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 94 133
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 94 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 94 133 (accept_3_3 23 94 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  94 133 (Polychromatic418967fa.accept_17_5_9_14_1_4282 22 94 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 94 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 94 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 94 133 (accept_3_3 20 94 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 94 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 94 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 94 133
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 94 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 94 133 (accept_3_3 17 94 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  94 133 (Polychromatic418967fa.accept_11_5_6_1_1_988 16 94 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 94 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 94 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 94 133 (accept_3_3 14 94 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 94 133 (Polychromatic418967fa.accept_18_13_4_7_1_4086 13 94 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 94 133
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 94 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 94 133 (accept_3_3 11 94 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  94 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 94 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 94 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 94 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 94 133 (accept_3_3 8 94 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 94 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 94 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 94 133
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 94 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 94 133 (accept_3_3 5 94 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 94
  133 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 94 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 94 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 94 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 94 133 (accept_3_3 2 94 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 94 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 94 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94 133))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 41 93 133 (Eq.refl Bool.true) (allA_succ_of_accept 40 93 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 40
  93 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 133
  (Polychromatic418967fa.accept_11_6_5_1_1_586 39 93 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 93 133 (accept_3_3 38 93 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  93 133 (Polychromatic418967fa.accept_9_1_3_7_1_6 37 93 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 93 133 (Polychromatic418967fa.accept_13_10_2_3_1_3025 36 93 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 93 133 (accept_3_3 35 93 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 93 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 133
  (Polychromatic418967fa.accept_9_6_3_7_1_580 33 93 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 93 133 (accept_3_3 32 93 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  93 133 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 93 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 93 133 (Polychromatic418967fa.accept_14_2_9_7_1_5633 30 93 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 93 133 (accept_3_3 29 93 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 93 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 133
  (Polychromatic418967fa.accept_12_3_9_1_1_290 27 93 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 93 133 (accept_3_3 26 93 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  93 133 (Polychromatic418967fa.accept_13_12_2_3_1_1527 25 93 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 93 133 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 93 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 93 133 (accept_3_3 23 93 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 93 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 133
  (Polychromatic418967fa.accept_22_21_5_1_1_6731 21 93 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 93 133 (accept_3_3 20 93 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  93 133 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 93 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 93 133 (Polychromatic418967fa.accept_13_5_2_3_1_1526 18 93 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 133 (accept_3_3 17 93 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 93 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 133
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 93 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 93 133 (accept_3_3 14 93 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  93 133 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 93 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 93 133 (Polychromatic418967fa.accept_13_12_2_3_1_1527 12 93 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 133 (accept_3_3 11 93 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 93 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 133
  (Polychromatic418967fa.accept_13_9_2_3_1_3027 9 93 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 93 133 (accept_3_3 8 93 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93
  133 (Polychromatic418967fa.accept_17_7_8_14_1_6720 7 93 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 93 133 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 93 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 133 (accept_3_3 5 93 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 93 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93 133
  (Polychromatic418967fa.accept_12_3_9_1_1_290 3 93 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 93 133 (accept_3_3 2 93 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93
  133 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 93 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 93 133))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 92 133 (Eq.refl Bool.true) (allA_of_3_1 42 92
  133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 91 133 (Eq.refl Bool.true) (allA_succ_of_gcd 42 91 133 7 6
  13 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 91 133
  (accept_3_3 41 91 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 91 133
  (Polychromatic418967fa.accept_9_4_1_7_1_293 40 91 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 91 133 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 91 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 91 133 (accept_3_3 38 91 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 91 133 (Polychromatic418967fa.accept_17_3_6_14_1_4312 37 91 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 91 133
  (Polychromatic418967fa.accept_22_14_3_1_1_6769 36 91 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 91 133 7 5 13 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 91 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 91 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 91 133 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 91 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 91 133 (accept_3_3 32 91 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 91 133 (Polychromatic418967fa.accept_9_4_1_7_1_293 31
  91 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 91 133
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 91 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 91 133 (accept_3_3 29 91 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 91
  133 7 4 13 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  91 133 (Polychromatic418967fa.accept_15_12_1_13_1_3444 27 91 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 91 133 (accept_3_3 26 91 133 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 91 133 (Polychromatic418967fa.accept_15_10_1_13_1_2609 25 91 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 91 133 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 91 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 91 133 (accept_3_3 23 91 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 91 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 22
  91 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 91 133 7 3 13 19 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 91 133 (accept_3_3 20
  91 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 91 133
  (Polychromatic418967fa.accept_23_19_22_18_1_6768 19 91 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 91 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 91 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 91 133 (accept_3_3 17 91 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 91 133 (Polychromatic418967fa.accept_18_16_1_7_1_4083 16 91 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 91 133
  (Polychromatic418967fa.accept_9_6_1_7_1_577 15 91 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 91 133 7 2 13 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 91 133 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 91 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 91 133 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 91 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 91 133 (accept_3_3 11 91 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 91 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 10
  91 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 133
  (Polychromatic418967fa.accept_16_9_11_5_1_2279 9 91 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 91 133 (accept_3_3 8 91 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 91 133
  7 1 13 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 91
  133 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 91 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 91 133 (accept_3_3 5 91 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91
  133 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 91 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 91 133 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 91 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 133 (accept_3_3 2 91 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 91 133 (Polychromatic418967fa.accept_23_1_22_18_1_6767 1 91 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91 133))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 90
  133 (Eq.refl Bool.true) (allA_succ_of_accept 43 90 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 90 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 90 133
  (Polychromatic418967fa.accept_20_2_10_13_1_6766 42 90 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 90 133 (accept_3_3 41 90 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  90 133 (Polychromatic418967fa.accept_22_18_2_1_1_6765 40 90 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 90 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 90 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 90 133 (accept_3_3 38 90 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 133 (Polychromatic418967fa.accept_20_17_10_13_1_1400 37 90 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 90 133
  (Polychromatic418967fa.accept_11_3_2_1_1_994 36 90 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 90 133 (accept_3_3 35 90 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  90 133 (Polychromatic418967fa.accept_21_13_6_7_1_1237 34 90 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 90 133 (Polychromatic418967fa.accept_21_12_6_7_1_3739 33 90 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 90 133 (accept_3_3 32 90 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 90 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 90 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 90 133
  (Polychromatic418967fa.accept_13_4_12_3_1_2999 30 90 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 90 133 (accept_3_3 29 90 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  90 133 (Polychromatic418967fa.accept_13_2_12_3_1_415 28 90 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 90 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 90 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 90 133 (accept_3_3 26 90 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 90 133 (Polychromatic418967fa.accept_11_3_2_1_1_994 25 90 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 90 133
  (Polychromatic418967fa.accept_21_3_6_7_1_6750 24 90 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 90 133 (accept_3_3 23 90 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  90 133 (Polychromatic418967fa.accept_13_9_12_3_1_907 22 90 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 90 133 (Polychromatic418967fa.accept_11_10_2_1_1_1036 21 90 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 90 133 (accept_3_3 20 90 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 90 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 90 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 90 133
  (Polychromatic418967fa.accept_21_18_6_7_1_6751 18 90 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 90 133 (accept_3_3 17 90 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  90 133 (Polychromatic418967fa.accept_21_16_6_7_1_6764 16 90 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 90 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 90 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 90 133 (accept_3_3 14 90 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 90 133 (Polychromatic418967fa.accept_14_13_6_7_1_2013 13 90 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 90 133
  (Polychromatic418967fa.accept_16_12_10_5_1_5457 12 90 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 90 133 (accept_3_3 11 90 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  90 133 (Polychromatic418967fa.accept_11_10_2_1_1_1036 10 90 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 90 133 (Polychromatic418967fa.accept_13_9_12_3_1_907 9 90 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 90 133 (accept_3_3 8 90 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 90 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 90 133
  (Polychromatic418967fa.accept_22_6_2_1_1_6763 6 90 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 90 133 (accept_3_3 5 90 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 90
  133 (Polychromatic418967fa.accept_13_4_12_3_1_2999 4 90 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 90 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 90 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 90 133 (accept_3_3 2 90 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 90 133 (Polychromatic418967fa.accept_14_1_6_7_1_1936 1 90 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90 133))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 45 89 133 (Eq.refl Bool.true) (allA_of_3_1 45 89 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  46 88 133 (Eq.refl Bool.true) (allA_succ_of_accept 45 88 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 88 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 88 133 (accept_3_3 44 88 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 88 133 (Polychromatic418967fa.accept_16_11_8_5_1_4366
  43 88 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 88 133
  (Polychromatic418967fa.accept_25_17_13_8_1_3187 42 88 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 88 133 (accept_3_3 41 88 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  88 133 (Polychromatic418967fa.accept_17_6_3_14_1_2078 40 88 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 88 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 88 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 88 133 (accept_3_3 38 88 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 88 133 (Polychromatic418967fa.accept_13_11_10_3_1_3020 37 88 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 88 133
  (Polychromatic418967fa.accept_10_6_8_3_1_930 36 88 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 88 133 (accept_3_3 35 88 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  88 133 (Polychromatic418967fa.accept_12_10_4_1_1_1843 34 88 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 88 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 88 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 88 133 (accept_3_3 32 88 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 88 133 (Polychromatic418967fa.accept_10_1_8_3_1_947 31 88 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 88 133
  (Polychromatic418967fa.accept_24_6_16_13_1_6762 30 88 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 88 133 (accept_3_3 29 88 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  88 133 (Polychromatic418967fa.accept_13_2_10_3_1_1538 28 88 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 88 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 88 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 88 133 (accept_3_3 26 88 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 88 133 (Polychromatic418967fa.accept_10_5_8_3_1_229 25 88 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 88 133
  (Polychromatic418967fa.accept_13_11_10_3_1_3020 24 88 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 88 133 (accept_3_3 23 88 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  88 133 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 88 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 88 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 88 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 88 133 (accept_3_3 20 88 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 88 133 (Polychromatic418967fa.accept_13_6_10_3_1_897 19 88 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 88 133
  (Polychromatic418967fa.accept_20_18_8_13_1_6761 18 88 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 88 133 (accept_3_3 17 88 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  88 133 (Polychromatic418967fa.accept_10_6_8_3_1_930 16 88 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 88 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 88 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 88 133 (accept_3_3 14 88 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 88 133 (Polychromatic418967fa.accept_16_13_8_5_1_3298 13 88 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 88 133
  (Polychromatic418967fa.accept_16_12_8_5_1_3316 12 88 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 88 133 (accept_3_3 11 88 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  88 133 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 88 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 88 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 88 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 88 133 (accept_3_3 8 88 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 88 133 (Polychromatic418967fa.accept_13_7_10_3_1_1505 7 88 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 88 133
  (Polychromatic418967fa.accept_10_6_8_3_1_930 6 88 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 88 133 (accept_3_3 5 88 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 88
  133 (Polychromatic418967fa.accept_16_4_8_5_1_3317 4 88 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 88 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 88 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 88 133 (accept_3_3 2 88 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 88 133 (Polychromatic418967fa.accept_10_1_8_3_1_947 1 88 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88 133))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 47 87 133 (Eq.refl Bool.true) (allA_succ_of_accept 46 87 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 46
  87 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 133
  (Polychromatic418967fa.accept_10_5_7_3_1_561 45 87 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 87 133 (accept_3_3 44 87 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  87 133 (Polychromatic418967fa.accept_16_11_7_5_1_4364 43 87 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 87 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 87 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 87 133 (accept_3_3 41 87 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 87 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 133
  (Polychromatic418967fa.accept_9_3_6_7_1_562 39 87 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 87 133 (accept_3_3 38 87 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  87 133 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 87 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 87 133 (Polychromatic418967fa.accept_10_6_7_3_1_547 36 87 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 87 133 (accept_3_3 35 87 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 87 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 133
  (Polychromatic418967fa.accept_12_9_3_1_1_303 33 87 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 87 133 (accept_3_3 32 87 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  87 133 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 87 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 87 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 87 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 133 (accept_3_3 29 87 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 87 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 133
  (Polychromatic418967fa.accept_16_11_7_5_1_4364 27 87 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 87 133 (accept_3_3 26 87 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  87 133 (Polychromatic418967fa.accept_10_5_7_3_1_561 25 87 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 87 133 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 87 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 133 (accept_3_3 23 87 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 87 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 133
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 87 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 87 133 (accept_3_3 20 87 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  87 133 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 87 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 87 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 87 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 133 (accept_3_3 17 87 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 87 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 133
  (Polychromatic418967fa.accept_10_5_7_3_1_561 15 87 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 87 133 (accept_3_3 14 87 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  87 133 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 87 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 87 133 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 87 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 133 (accept_3_3 11 87 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 87 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 133
  (Polychromatic418967fa.accept_11_9_10_1_1_581 9 87 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 87 133 (accept_3_3 8 87 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87
  133 (Polychromatic418967fa.accept_13_7_9_3_1_1504 7 87 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 87 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 87 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 133 (accept_3_3 5 87 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 87 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 133
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 87 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 87 133 (accept_3_3 2 87 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87
  133 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 87 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 87 133))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 86 133 (Eq.refl Bool.true) (allA_of_3_1
  48 86 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 85 133 (Eq.refl Bool.true) (allA_succ_of_accept 48
  85 133 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 85 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 85 133 (accept_3_3 47 85 133 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 85 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 85 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 85 133 (Polychromatic418967fa.accept_21_3_1_7_1_5187 45 85 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 85 133 (accept_3_3 44 85 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 133 (Polychromatic418967fa.accept_13_4_7_3_1_92 43
  85 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 85 133
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 85 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 85 133 (accept_3_3 41 85 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  85 133 (Polychromatic418967fa.accept_13_1_7_3_1_1503 40 85 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 85 133 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 85 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 85 133 (accept_3_3 38 85 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 85 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 85 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 133
  (Polychromatic418967fa.accept_13_10_7_3_1_3041 36 85 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 85 133 (accept_3_3 35 85 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  85 133 (Polychromatic418967fa.accept_13_8_7_3_1_430 34 85 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 85 133 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 85 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 133 (accept_3_3 32 85 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 85 133 (Polychromatic418967fa.accept_15_1_10_13_1_939 31 85 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 85 133
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 85 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 85 133 (accept_3_3 29 85 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  85 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 85 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 85 133 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 85 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 133 (accept_3_3 26 85 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 85 133 (Polychromatic418967fa.accept_21_4_1_7_1_3771 25 85 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 85 133
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 85 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 85 133 (accept_3_3 23 85 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  85 133 (Polychromatic418967fa.accept_10_2_5_3_1_1408 22 85 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 85 133 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 85 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 85 133 (accept_3_3 20 85 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 85 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 85 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 133
  (Polychromatic418967fa.accept_10_8_5_3_1_543 18 85 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 85 133 (accept_3_3 17 85 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  85 133 (Polychromatic418967fa.accept_15_1_10_13_1_939 16 85 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 85 133 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 85 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 85 133 (accept_3_3 14 85 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 133 (Polychromatic418967fa.accept_14_13_1_7_1_1211 13 85 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 133
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 85 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 133 (accept_3_3 11 85 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  85 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 85 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 85 133 (Polychromatic418967fa.accept_13_9_7_3_1_1531 9 85 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 133 (accept_3_3 8 85 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 133 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 85 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 133
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 85 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 85 133 (accept_3_3 5 85 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85
  133 (Polychromatic418967fa.accept_11_4_8_1_1_1047 4 85 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 85 133 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 85 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 133 (accept_3_3 2 85 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 85 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 85 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85 133)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 50 84 133 (Eq.refl Bool.true) (allA_succ_of_gcd 49 84 133 7 7 12 19 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 84 133
  (Polychromatic418967fa.accept_13_9_6_3_1_1514 48 84 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 84 133 (accept_3_3 47 84 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  84 133 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 84 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 84 133 (Polychromatic418967fa.accept_17_11_16_14_1_6760 45 84 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 84 133 (accept_3_3 44 84 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 84 133 (Polychromatic418967fa.accept_20_3_4_13_1_3824 43 84
  133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 133 7 6 12 19 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 133 (accept_3_3 41
  84 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 84 133
  (Polychromatic418967fa.accept_9_4_3_7_1_296 40 84 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 84 133 (Polychromatic418967fa.accept_10_9_4_3_1_539 39 84 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 84 133 (accept_3_3 38 84 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 84 133 (Polychromatic418967fa.accept_9_1_3_7_1_6 37 84 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 84 133 (Polychromatic418967fa.accept_13_10_6_3_1_1515
  36 84 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 84 133 7 5 12 19 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 84 133
  (Polychromatic418967fa.accept_15_4_9_13_1_2582 34 84 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 84 133 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 84 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 84 133 (accept_3_3 32 84 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 84 133 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 84 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 84 133 (Polychromatic418967fa.accept_22_8_18_1_1_6759
  30 84 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 84 133 (accept_3_3 29
  84 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 84 133 7 4 12 19 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 84 133
  (Polychromatic418967fa.accept_10_7_4_3_1_560 27 84 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 84 133 (accept_3_3 26 84 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  84 133 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 84 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 84 133 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 84 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 84 133 (accept_3_3 23 84 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 84 133 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 84 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 84 133 7 3 12 19 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 84 133 (accept_3_3 20 84 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 133 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 84 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 84 133
  (Polychromatic418967fa.accept_13_5_6_3_1_868 18 84 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 84 133 (accept_3_3 17 84 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  84 133 (Polychromatic418967fa.accept_24_16_12_13_1_1854 16 84 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 84 133 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 84 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 84 133 7 2 12 19 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 133 (Polychromatic418967fa.accept_9_4_3_7_1_296 13
  84 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 84 133
  (Polychromatic418967fa.accept_16_12_4_5_1_2273 12 84 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 84 133 (accept_3_3 11 84 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  84 133 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 84 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 84 133 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 84 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 84 133 (accept_3_3 8 84 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 7 84 133 7 1 12 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 6 84 133 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 84 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 84 133 (accept_3_3 5 84 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 84 133 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 84 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 84 133
  (Polychromatic418967fa.accept_15_3_9_13_1_1681 3 84 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 84 133 (accept_3_3 2 84 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84
  133 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 84 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 84 133)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 83 133 (Eq.refl Bool.true)
  (allA_of_3_1 51 83 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 52 82 133 (Eq.refl Bool.true)
  (allA_succ_of_accept 51 82 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 82 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 82 133 (accept_3_3 50 82 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 82 133 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 82 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 82 133 (Polychromatic418967fa.accept_9_3_1_7_1_97 48
  82 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 82 133 (accept_3_3 47 82
  133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 82 133
  (Polychromatic418967fa.accept_13_7_4_3_1_3064 46 82 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 82 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 82 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 82 133 (accept_3_3 44 82 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 82 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 82 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 82 133 (Polychromatic418967fa.accept_9_6_1_7_1_577 42
  82 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 82 133 (accept_3_3 41 82
  133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 82 133
  (Polychromatic418967fa.accept_9_4_1_7_1_293 40 82 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 82 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 82 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 82 133 (accept_3_3 38 82 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 82 133 (Polychromatic418967fa.accept_14_9_12_7_1_597 37 82 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 82 133 (Polychromatic418967fa.accept_15_6_7_13_1_1666
  36 82 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 82 133 (accept_3_3 35
  82 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 82 133
  (Polychromatic418967fa.accept_21_13_19_7_1_5162 34 82 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 82 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 82 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 82 133 (accept_3_3 32 82 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 82 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 82 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 82 133 (Polychromatic418967fa.accept_9_3_1_7_1_97 30
  82 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 82 133 (accept_3_3 29 82
  133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 82 133
  (Polychromatic418967fa.accept_11_6_5_1_1_586 28 82 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 82 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 82 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 82 133 (accept_3_3 26 82 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 82 133 (Polychromatic418967fa.accept_10_5_2_3_1_239 25 82 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 82 133 (Polychromatic418967fa.accept_9_6_1_7_1_577 24
  82 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 82 133 (accept_3_3 23 82
  133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 82 133
  (Polychromatic418967fa.accept_9_4_1_7_1_293 22 82 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 82 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 82 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 82 133 (accept_3_3 20 82 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 82 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 82 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 82 133
  (Polychromatic418967fa.accept_20_18_2_13_1_5265 18 82 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 82 133 (accept_3_3 17 82 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  82 133 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 82 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 82 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 82 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 82 133 (accept_3_3 14 82 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 82 133 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 82 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 82 133
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 82 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 82 133 (accept_3_3 11 82 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  82 133 (Polychromatic418967fa.accept_20_10_2_13_1_2560 10 82 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 82 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 82 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 82 133 (accept_3_3 8 82 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 82 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 82 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 82 133
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 82 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 82 133 (accept_3_3 5 82 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 82
  133 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 82 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 82 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 82 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 133 (accept_3_3 2 82 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 82 133 (Polychromatic418967fa.accept_10_1_2_3_1_1910 1 82 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82 133))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 53 81 133 (Eq.refl Bool.true) (allA_succ_of_accept 52 81 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 52
  81 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 133
  (Polychromatic418967fa.accept_12_3_9_1_1_290 51 81 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 81 133 (accept_3_3 50 81 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  81 133 (Polychromatic418967fa.accept_15_4_6_13_1_956 49 81 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 81 133 (Polychromatic418967fa.accept_10_8_1_3_1_1374 48 81 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 133 (accept_3_3 47 81 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 81 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 133
  (Polychromatic418967fa.accept_14_3_11_7_1_1260 45 81 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 81 133 (accept_3_3 44 81 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  81 133 (Polychromatic418967fa.accept_20_3_1_13_1_6742 43 81 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 81 133 (Polychromatic418967fa.accept_10_2_1_3_1_233 42 81 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 133 (accept_3_3 41 81 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 81 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 133
  (Polychromatic418967fa.accept_12_3_9_1_1_290 39 81 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 81 133 (accept_3_3 38 81 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  81 133 (Polychromatic418967fa.accept_15_7_6_13_1_936 37 81 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 81 133 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 81 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 133 (accept_3_3 35 81 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 81 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 133
  (Polychromatic418967fa.accept_21_12_18_7_1_6740 33 81 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 81 133 (accept_3_3 32 81 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  81 133 (Polychromatic418967fa.accept_14_3_11_7_1_1260 31 81 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 81 133 (Polychromatic418967fa.accept_11_8_4_1_1_1000 30 81 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 133 (accept_3_3 29 81 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 81 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 133
  (Polychromatic418967fa.accept_12_3_9_1_1_290 27 81 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 81 133 (accept_3_3 26 81 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  81 133 (Polychromatic418967fa.accept_16_9_1_5_1_2282 25 81 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 81 133 (Polychromatic418967fa.accept_14_10_11_7_1_1955 24 81 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 133 (accept_3_3 23 81 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 81 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 133
  (Polychromatic418967fa.accept_17_4_13_14_1_1139 21 81 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 81 133 (accept_3_3 20 81 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  81 133 (Polychromatic418967fa.accept_11_8_4_1_1_1000 19 81 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 81 133 (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 81 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 133 (accept_3_3 17 81 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 81 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 133
  (Polychromatic418967fa.accept_12_3_9_1_1_290 15 81 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 81 133 (accept_3_3 14 81 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  81 133 (Polychromatic418967fa.accept_16_13_1_5_1_5469 13 81 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 81 133 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 81 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 133 (accept_3_3 11 81 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 81 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 133
  (Polychromatic418967fa.accept_16_9_1_5_1_2282 9 81 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 81 133 (accept_3_3 8 81 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81
  133 (Polychromatic418967fa.accept_15_7_6_13_1_936 7 81 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 81 133 (Polychromatic418967fa.accept_16_6_1_5_1_2242 6 81 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 133 (accept_3_3 5 81 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 81 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 133
  (Polychromatic418967fa.accept_12_3_9_1_1_290 3 81 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 81 133 (accept_3_3 2 81 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81
  133 (Polychromatic418967fa.accept_17_1_13_14_1_478 1 81 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 81 133))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 80 133 (Eq.refl
  Bool.true) (allA_of_3_1 54 80 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 55 79 133 (Eq.refl Bool.true)
  (allA_succ_of_accept 54 79 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 79 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 79 133 (accept_3_3 53 79 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 79 133 (Polychromatic418967fa.accept_16_4_15_5_1_5537 52 79 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 79 133
  (Polychromatic418967fa.accept_15_6_4_13_1_403 51 79 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 79 133 (accept_3_3 50 79 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  79 133 (Polychromatic418967fa.accept_16_1_15_5_1_708 49 79 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 79 133 (Polychromatic418967fa.accept_21_6_16_7_1_3714 48 79 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 79 133 (accept_3_3 47 79 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 79 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 79 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 79 133
  (Polychromatic418967fa.accept_13_6_1_3_1_1522 45 79 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 79 133 (accept_3_3 44 79 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  79 133 (Polychromatic418967fa.accept_11_10_2_1_1_1036 43 79 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 79 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 79 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 79 133 (accept_3_3 41 79 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 79 133 (Polychromatic418967fa.accept_14_12_9_7_1_2762 40 79 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 79 133
  (Polychromatic418967fa.accept_15_9_4_13_1_4482 39 79 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 79 133 (accept_3_3 38 79 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  79 133 (Polychromatic418967fa.accept_13_11_1_3_1_910 37 79 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 79 133 (Polychromatic418967fa.accept_10_6_9_3_1_935 36 79 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 79 133 (accept_3_3 35 79 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 79 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 79 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 79 133
  (Polychromatic418967fa.accept_13_7_1_3_1_1523 33 79 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 79 133 (accept_3_3 32 79 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  79 133 (Polychromatic418967fa.accept_13_5_1_3_1_878 31 79 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 79 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 79 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 79 133 (accept_3_3 29 79 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 79 133 (Polychromatic418967fa.accept_13_2_1_3_1_419 28 79 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 79 133
  (Polychromatic418967fa.accept_21_6_16_7_1_3714 27 79 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 79 133 (accept_3_3 26 79 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  79 133 (Polychromatic418967fa.accept_11_3_2_1_1_994 25 79 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 79 133 (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 79 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 79 133 (accept_3_3 23 79 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 79 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 79 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 79 133
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 21 79 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 79 133 (accept_3_3 20 79 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  79 133 (Polychromatic418967fa.accept_13_6_1_3_1_1522 19 79 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 79 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 79 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 79 133 (accept_3_3 17 79 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 79 133 (Polychromatic418967fa.accept_10_6_9_3_1_935 16 79 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 79 133
  (Polychromatic418967fa.accept_13_2_1_3_1_419 15 79 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 79 133 (accept_3_3 14 79 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  79 133 (Polychromatic418967fa.accept_21_13_16_7_1_3712 13 79 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 79 133 (Polychromatic418967fa.accept_14_12_9_7_1_2762 12 79 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 79 133 (accept_3_3 11 79 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 79 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 79 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 79 133
  (Polychromatic418967fa.accept_15_9_4_13_1_4482 9 79 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 79 133 (accept_3_3 8 79 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 79
  133 (Polychromatic418967fa.accept_13_7_1_3_1_1523 7 79 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 79 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 79 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 79 133 (accept_3_3 5 79 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 79 133 (Polychromatic418967fa.accept_10_4_9_3_1_1907 4 79 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 79 133
  (Polychromatic418967fa.accept_11_3_2_1_1_994 3 79 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 79 133 (accept_3_3 2 79 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 79
  133 (Polychromatic418967fa.accept_16_1_15_5_1_708 1 79 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 79 133))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 78 133 (Eq.refl
  Bool.true) (allA_succ_of_accept 55 78 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 78 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 78 133 (Polychromatic418967fa.accept_15_9_3_13_1_1686
  54 78 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 78 133 (accept_3_3 53
  78 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 78 133
  (Polychromatic418967fa.accept_17_1_10_14_1_1173 52 78 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 78 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 78 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 78 133 (accept_3_3 50 78 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 78 133 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 78 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 78 133 (Polychromatic418967fa.accept_9_3_6_7_1_562 48
  78 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 78 133 (accept_3_3 47 78
  133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 78 133
  (Polychromatic418967fa.accept_9_1_6_7_1_285 46 78 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 78 133 (Polychromatic418967fa.accept_10_5_8_3_1_229 45 78 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 78 133 (accept_3_3 44 78 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 78 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 78 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 78 133
  (Polychromatic418967fa.accept_15_12_3_13_1_4481 42 78 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 78 133 (accept_3_3 41 78 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  78 133 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 78 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 78 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 78 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 78 133 (accept_3_3 38 78 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 78 133 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 78 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 78 133
  (Polychromatic418967fa.accept_10_6_8_3_1_930 36 78 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 78 133 (accept_3_3 35 78 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  78 133 (Polychromatic418967fa.accept_14_6_8_7_1_589 34 78 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 78 133 (Polychromatic418967fa.accept_21_12_15_7_1_6758 33 78 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 78 133 (accept_3_3 32 78 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 78 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 78 133
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 78 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 78 133 (accept_3_3 29 78 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  78 133 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 78 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 78 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 78 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 78 133 (accept_3_3 26 78 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 133 (Polychromatic418967fa.accept_10_5_8_3_1_229 25 78 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 78 133
  (Polychromatic418967fa.accept_15_9_3_13_1_1686 24 78 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 78 133 (accept_3_3 23 78 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  78 133 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 78 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 78 133 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 78 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 78 133 (accept_3_3 20 78 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 78 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 133
  (Polychromatic418967fa.accept_17_1_10_14_1_1173 18 78 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 78 133 (accept_3_3 17 78 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  78 133 (Polychromatic418967fa.accept_10_6_8_3_1_930 16 78 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 78 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 78 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 78 133 (accept_3_3 14 78 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 133 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 78 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 78 133
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 78 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 78 133 (accept_3_3 11 78 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  78 133 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 78 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 78 133 (Polychromatic418967fa.accept_15_9_3_13_1_1686 9 78 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 78 133 (accept_3_3 8 78 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 78 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 78 133
  (Polychromatic418967fa.accept_10_6_8_3_1_930 6 78 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 78 133 (accept_3_3 5 78 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78
  133 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 78 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 78 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 78 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 78 133 (accept_3_3 2 78 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 78 133 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 78 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78 133))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 57 77 133 (Eq.refl Bool.true) (allA_of_3_1 57 77 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  58 76 133 (Eq.refl Bool.true) (allA_succ_of_gcd 57 76 133 19 3 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 76 133 (accept_3_3 56 76 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 76 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 76 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 76 133 (Polychromatic418967fa.accept_13_2_11_3_1_873
  54 76 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 76 133 (accept_3_3 53
  76 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 76 133
  (Polychromatic418967fa.accept_16_4_12_5_1_2287 52 76 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 76 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 76 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 76 133 (accept_3_3 50 76 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 76 133 (Polychromatic418967fa.accept_8_1_4_5_1_48 49 76 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 76 133 (Polychromatic418967fa.accept_9_3_4_7_1_89 48
  76 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 76 133 (accept_3_3 47 76
  133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 76 133 (Polychromatic418967fa.accept_9_1_4_7_1_7
  46 76 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 76 133
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 76 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 76 133 (accept_3_3 44 76 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  76 133 (Polychromatic418967fa.accept_14_1_6_7_1_1936 43 76 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 76 133 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 76 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 76 133 (accept_3_3 41 76 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 76 133 (Polychromatic418967fa.accept_13_1_11_3_1_901 40 76 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 76 133
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 76 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 76 133 19 2 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 76 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 76 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 76 133 (Polychromatic418967fa.accept_13_10_11_3_1_1518 36 76
  133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 76 133 (accept_3_3 35 76 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 76 133 (Polychromatic418967fa.accept_12_10_4_1_1_1843
  34 76 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 76 133
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 76 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 76 133 (accept_3_3 32 76 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  76 133 (Polychromatic418967fa.accept_11_9_10_1_1_581 31 76 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 76 133 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 76 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 76 133 (accept_3_3 29 76 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 76 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 76 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 76 133
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 76 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 76 133 (accept_3_3 26 76 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  76 133 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 76 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 76 133 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 76 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 76 133 (accept_3_3 23 76 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 76 133 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 76 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 76 133
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 76 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 76 133 (accept_3_3 20 76 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 19 76
  133 19 1 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 18
  76 133 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 76 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 76 133 (accept_3_3 17 76 133 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 76 133 (Polychromatic418967fa.accept_17_16_8_14_1_6757 16 76 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 76 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 76 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 76 133 (accept_3_3 14 76 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 76 133 (Polychromatic418967fa.accept_11_2_10_1_1_1017
  13 76 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 76 133
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 76 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 76 133 (accept_3_3 11 76 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  76 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 76 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 76 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 76 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 76 133 (accept_3_3 8 76 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 76 133 (Polychromatic418967fa.accept_10_7_6_3_1_927 7 76 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 76 133
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 76 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 76 133 (accept_3_3 5 76 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 76
  133 (Polychromatic418967fa.accept_16_4_12_5_1_2287 4 76 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 76 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 76 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 76 133 (accept_3_3 2 76 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 76 133 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 76 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76
  133)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 75 133 (Eq.refl Bool.true)
  (allA_succ_of_accept 58 75 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 75 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 133 (Polychromatic418967fa.accept_10_7_5_3_1_542 57 75 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 133 (accept_3_3 56 75 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 75 133 (Polychromatic418967fa.accept_9_1_3_7_1_6 55
  75 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 75 133
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 75 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 75 133 (accept_3_3 53 75 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  75 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 75 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 75 133 (Polychromatic418967fa.accept_9_6_3_7_1_580 51 75 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 133 (accept_3_3 50 75 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 75 133 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 75 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 75 133
  (Polychromatic418967fa.accept_10_8_5_3_1_543 48 75 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 75 133 (accept_3_3 47 75 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  75 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 75 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 75 133 (Polychromatic418967fa.accept_12_9_3_1_1_303 45 75 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 133 (accept_3_3 44 75 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 133 (Polychromatic418967fa.accept_11_10_9_1_1_2186 43 75 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 75 133
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 75 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 75 133 (accept_3_3 41 75 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  75 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 75 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 75 133 (Polychromatic418967fa.accept_16_7_11_5_1_4402 39 75 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 133 (accept_3_3 38 75 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 133 (Polychromatic418967fa.accept_9_1_3_7_1_6 37 75 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 75 133
  (Polychromatic418967fa.accept_21_15_12_7_1_5204 36 75 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 75 133 (accept_3_3 35 75 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  75 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 75 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 75 133 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 75 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 133 (accept_3_3 32 75 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 133 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 75 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 75 133
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 75 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 75 133 (accept_3_3 29 75 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  75 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 75 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 75 133 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 75 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 133 (accept_3_3 26 75 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 133 (Polychromatic418967fa.accept_16_9_11_5_1_2279 25 75 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 75 133
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 75 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 75 133 (accept_3_3 23 75 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  75 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 75 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 75 133 (Polychromatic418967fa.accept_11_10_9_1_1_2186 21 75 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 133 (accept_3_3 20 75 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 133 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 75 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 133
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 75 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 75 133 (accept_3_3 17 75 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  75 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 75 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 75 133 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 75 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 133 (accept_3_3 14 75 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 133 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 75 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 75 133
  (Polychromatic418967fa.accept_10_2_5_3_1_1408 12 75 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 75 133 (accept_3_3 11 75 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  75 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 75 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 75 133 (Polychromatic418967fa.accept_12_9_3_1_1_303 9 75 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 133 (accept_3_3 8 75 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 133 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 75 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 133
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 75 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 133 (accept_3_3 5 75 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75
  133 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 75 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 75 133 (Polychromatic418967fa.accept_21_3_12_7_1_3755 3 75 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 133 (accept_3_3 2 75 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 75 133 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 75 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75 133)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 60 74 133 (Eq.refl Bool.true) (allA_of_3_1 60 74 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  61 73 133 (Eq.refl Bool.true) (allA_succ_of_accept 60 73 133 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 73 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 73 133 (accept_3_3 59 73 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 73 133 (Polychromatic418967fa.accept_9_4_1_7_1_293 58
  73 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 73 133
  (Polychromatic418967fa.accept_9_3_1_7_1_97 57 73 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 73 133 (accept_3_3 56 73 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  73 133 (Polychromatic418967fa.accept_21_13_10_7_1_3701 55 73 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 73 133 (Polychromatic418967fa.accept_23_8_4_18_1_6756 54 73 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 73 133 (accept_3_3 53 73 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 73 133 (Polychromatic418967fa.accept_8_4_1_5_1_186 52 73 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 73 133
  (Polychromatic418967fa.accept_9_6_1_7_1_577 51 73 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 73 133 (accept_3_3 50 73 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  73 133 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 73 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 73 133 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 73 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 73 133 (accept_3_3 47 73 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 73 133 (Polychromatic418967fa.accept_13_7_8_3_1_1533 46 73 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 73 133
  (Polychromatic418967fa.accept_16_13_9_5_1_3302 45 73 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 73 133 (accept_3_3 44 73 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  73 133 (Polychromatic418967fa.accept_16_11_9_5_1_4412 43 73 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 73 133 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 73 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 73 133 (accept_3_3 41 73 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 73 133 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 73 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 73 133
  (Polychromatic418967fa.accept_9_3_1_7_1_97 39 73 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 73 133 (accept_3_3 38 73 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  73 133 (Polychromatic418967fa.accept_13_11_8_3_1_3016 37 73 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 73 133 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 73 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 73 133 (accept_3_3 35 73 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 73 133 (Polychromatic418967fa.accept_18_16_1_7_1_4083 34 73 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 73 133
  (Polychromatic418967fa.accept_9_6_1_7_1_577 33 73 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 73 133 (accept_3_3 32 73 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  73 133 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 73 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 73 133 (Polychromatic418967fa.accept_9_3_1_7_1_97 30 73 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 73 133 (accept_3_3 29 73 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 73 133 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 73 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 73 133
  (Polychromatic418967fa.accept_16_11_9_5_1_4412 27 73 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 73 133 (accept_3_3 26 73 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  73 133 (Polychromatic418967fa.accept_14_11_3_7_1_604 25 73 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 73 133 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 73 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 73 133 (accept_3_3 23 73 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 73 133 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 73 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 73 133
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 73 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 73 133 (accept_3_3 20 73 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  73 133 (Polychromatic418967fa.accept_17_2_5_14_1_2068 19 73 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 73 133 (Polychromatic418967fa.accept_13_5_8_3_1_1535 18 73 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 73 133 (accept_3_3 17 73 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 73 133 (Polychromatic418967fa.accept_18_16_1_7_1_4083 16 73 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 73 133
  (Polychromatic418967fa.accept_9_6_1_7_1_577 15 73 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 73 133 (accept_3_3 14 73 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  73 133 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 73 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 73 133 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 73 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 73 133 (accept_3_3 11 73 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 73 133 (Polychromatic418967fa.accept_14_10_3_7_1_1975 10 73 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 73 133
  (Polychromatic418967fa.accept_13_9_8_3_1_3045 9 73 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 73 133 (accept_3_3 8 73 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 73
  133 (Polychromatic418967fa.accept_13_7_8_3_1_1533 7 73 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 73 133 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 73 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 73 133 (accept_3_3 5 73 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 73 133 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 73 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 73 133
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 73 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 73 133 (accept_3_3 2 73 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 73
  133 (Polychromatic418967fa.accept_16_1_9_5_1_5443 1 73 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 73 133))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 72 133
  (Eq.refl Bool.true) (allA_succ_of_accept 61 72 133 (Polychromatic418967fa.accept_10_1_2_3_1_1910 61 72 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 72 133
  (Polychromatic418967fa.accept_11_5_6_1_1_988 60 72 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 72 133 (accept_3_3 59 72 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  72 133 (Polychromatic418967fa.accept_17_7_4_14_1_2106 58 72 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 72 133 (Polychromatic418967fa.accept_21_15_9_7_1_3780 57 72 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 72 133 (accept_3_3 56 72 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 133 (Polychromatic418967fa.accept_10_5_2_3_1_239 55 72 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 72 133
  (Polychromatic418967fa.accept_14_12_2_7_1_1243 54 72 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 72 133 (accept_3_3 53 72 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  72 133 (Polychromatic418967fa.accept_16_4_8_5_1_3317 52 72 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 72 133 (Polychromatic418967fa.accept_10_1_2_3_1_1910 51 72 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 72 133 (accept_3_3 50 72 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 72 133 (Polychromatic418967fa.accept_11_5_6_1_1_988 49 72 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 72 133
  (Polychromatic418967fa.accept_13_9_7_3_1_1531 48 72 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 72 133 (accept_3_3 47 72 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  72 133 (Polychromatic418967fa.accept_15_1_12_13_1_944 46 72 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 72 133 (Polychromatic418967fa.accept_10_5_2_3_1_239 45 72 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 72 133 (accept_3_3 44 72 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 133 (Polychromatic418967fa.accept_13_4_7_3_1_92 43 72 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 72 133
  (Polychromatic418967fa.accept_25_17_22_8_1_6755 42 72 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 72 133 (accept_3_3 41 72 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  72 133 (Polychromatic418967fa.accept_11_7_6_1_1_2182 40 72 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 72 133 (Polychromatic418967fa.accept_20_19_12_13_1_2602 39 72 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 72 133 (accept_3_3 38 72 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 133 (Polychromatic418967fa.accept_13_11_7_3_1_894 37 72 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 72 133
  (Polychromatic418967fa.accept_13_10_7_3_1_3041 36 72 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 72 133 (accept_3_3 35 72 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  72 133 (Polychromatic418967fa.accept_13_8_7_3_1_430 34 72 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 72 133 (Polychromatic418967fa.accept_14_5_2_7_1_2804 33 72 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 72 133 (accept_3_3 32 72 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 72 133 (Polychromatic418967fa.accept_10_1_2_3_1_1910 31 72 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 72 133
  (Polychromatic418967fa.accept_13_4_7_3_1_92 30 72 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 72 133 (accept_3_3 29 72 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  72 133 (Polychromatic418967fa.accept_16_12_8_5_1_3316 28 72 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 72 133 (Polychromatic418967fa.accept_11_5_6_1_1_988 27 72 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 72 133 (accept_3_3 26 72 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 133 (Polychromatic418967fa.accept_10_5_2_3_1_239 25 72 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 72 133
  (Polychromatic418967fa.accept_13_11_7_3_1_894 24 72 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 72 133 (accept_3_3 23 72 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  72 133 (Polychromatic418967fa.accept_13_9_7_3_1_1531 22 72 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 72 133 (Polychromatic418967fa.accept_10_1_2_3_1_1910 21 72 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 72 133 (accept_3_3 20 72 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 133 (Polychromatic418967fa.accept_14_5_2_7_1_2804 19 72 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 72 133
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 72 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 72 133 (accept_3_3 17 72 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  72 133 (Polychromatic418967fa.accept_11_5_6_1_1_988 16 72 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 72 133 (Polychromatic418967fa.accept_10_5_2_3_1_239 15 72 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 72 133 (accept_3_3 14 72 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 133 (Polychromatic418967fa.accept_16_13_8_5_1_3298 13 72 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 72 133
  (Polychromatic418967fa.accept_14_12_2_7_1_1243 12 72 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 72 133 (accept_3_3 11 72 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  72 133 (Polychromatic418967fa.accept_13_10_7_3_1_3041 10 72 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 72 133 (Polychromatic418967fa.accept_13_9_7_3_1_1531 9 72 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 72 133 (accept_3_3 8 72 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 133 (Polychromatic418967fa.accept_11_7_6_1_1_2182 7 72 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 72 133
  (Polychromatic418967fa.accept_21_6_9_7_1_3752 6 72 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 72 133 (accept_3_3 5 72 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 72
  133 (Polychromatic418967fa.accept_13_4_7_3_1_92 4 72 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 72 133 (Polychromatic418967fa.accept_15_3_12_13_1_2549 3 72 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 72 133 (accept_3_3 2 72 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 72 133 (Polychromatic418967fa.accept_10_1_2_3_1_1910 1 72 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72
  133)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 71 133 (Eq.refl Bool.true)
  (allA_of_3_1 63 71 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 64 70 133 (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 70 133 7 9 10 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 70 133 (accept_3_3 62 70 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  70 133 (Polychromatic418967fa.accept_13_9_5_3_1_428 61 70 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 70 133 (Polychromatic418967fa.accept_13_8_5_3_1_427 60 70 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 70 133 (accept_3_3 59 70 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 70 133 (Polychromatic418967fa.accept_13_6_5_3_1_426 58 70 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 70 133
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 70 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 70 133 7 8 10 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 70 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 70 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 70 133 (Polychromatic418967fa.accept_13_2_5_3_1_406 54 70 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 70 133 (accept_3_3 53 70 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 70 133 (Polychromatic418967fa.accept_11_8_4_1_1_1000
  52 70 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 70 133
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 70 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 70 133 (accept_3_3 50 70 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 70
  133 7 7 10 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48
  70 133 (Polychromatic418967fa.accept_13_9_5_3_1_428 48 70 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 70 133 (accept_3_3 47 70 133 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 70 133 (Polychromatic418967fa.accept_15_1_10_13_1_939 46 70 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 70 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 70 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 70 133 (accept_3_3 44 70 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 70 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 43
  70 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 70 133 7 6 10 19 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 70 133 (accept_3_3 41
  70 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 70 133
  (Polychromatic418967fa.accept_12_4_10_1_1_706 40 70 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 70 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 70 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 70 133 (accept_3_3 38 70 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 70 133 (Polychromatic418967fa.accept_13_11_5_3_1_889 37 70 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 70 133 (Polychromatic418967fa.accept_16_4_6_5_1_2245
  36 70 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 70 133 7 5 10 19 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 70 133
  (Polychromatic418967fa.accept_13_8_5_3_1_427 34 70 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 70 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 70 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 70 133 (accept_3_3 32 70 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 70 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 70 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 70 133 (Polychromatic418967fa.accept_11_8_4_1_1_1000
  30 70 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 70 133 (accept_3_3 29
  70 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 70 133 7 4 10 19 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 70 133
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 70 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 70 133 (accept_3_3 26 70 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  70 133 (Polychromatic418967fa.accept_20_5_10_13_1_6754 25 70 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 70 133 (Polychromatic418967fa.accept_13_11_5_3_1_889 24 70 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 70 133 (accept_3_3 23 70 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 70 133 (Polychromatic418967fa.accept_13_9_5_3_1_428 22 70 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 70 133 7 3 10 19 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 70 133 (accept_3_3 20 70 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 70 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 70 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 70 133
  (Polychromatic418967fa.accept_15_3_10_13_1_2605 18 70 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 70 133 (accept_3_3 17 70 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  70 133 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 70 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 70 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 70 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 70 133 7 2 10 19 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 70 133 (Polychromatic418967fa.accept_22_13_4_1_1_6753
  13 70 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 70 133
  (Polychromatic418967fa.accept_15_12_10_13_1_4497 12 70 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 70 133 (accept_3_3 11 70 133 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 70 133 (Polychromatic418967fa.accept_26_10_18_3_1_6752 10 70 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 70 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 70 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 70 133 (accept_3_3 8 70 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 70 133 7 1 10 19 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 70 133 (Polychromatic418967fa.accept_13_6_5_3_1_426 6
  70 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 70 133 (accept_3_3 5 70 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 70 133 (Polychromatic418967fa.accept_12_4_10_1_1_706 4
  70 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 70 133
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 70 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 70 133 (accept_3_3 2 70 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 70
  133 (Polychromatic418967fa.accept_13_1_5_3_1_888 1 70 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 70 133)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 69 133 (Eq.refl
  Bool.true) (allA_succ_of_accept 64 69 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 69 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 133 (Polychromatic418967fa.accept_12_3_9_1_1_290
  63 69 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 133 (accept_3_3 62
  69 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 133
  (Polychromatic418967fa.accept_17_10_1_14_1_489 61 69 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 69 133 (Polychromatic418967fa.accept_21_18_6_7_1_6751 60 69 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 69 133 (accept_3_3 59 69 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 69 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 69 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 133 (Polychromatic418967fa.accept_9_3_6_7_1_562 57
  69 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 133 (accept_3_3 56 69
  133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 69 133
  (Polychromatic418967fa.accept_9_1_6_7_1_285 55 69 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 69 133 (Polychromatic418967fa.accept_10_4_9_3_1_1907 54 69 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 69 133 (accept_3_3 53 69 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 69 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 69 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 133 (Polychromatic418967fa.accept_12_3_9_1_1_290
  51 69 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 133 (accept_3_3 50
  69 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 133
  (Polychromatic418967fa.accept_9_4_6_7_1_286 49 69 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 69 133 (Polychromatic418967fa.accept_9_3_6_7_1_562 48 69 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 69 133 (accept_3_3 47 69 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 69 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 69 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 133 (Polychromatic418967fa.accept_21_3_6_7_1_6750
  45 69 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 133 (accept_3_3 44
  69 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 133
  (Polychromatic418967fa.accept_14_1_13_7_1_1205 43 69 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 69 133 (Polychromatic418967fa.accept_20_2_9_13_1_2599 42 69 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 69 133 (accept_3_3 41 69 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 69 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 69 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 133 (Polychromatic418967fa.accept_9_3_6_7_1_562 39
  69 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 133 (accept_3_3 38 69
  133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 69 133
  (Polychromatic418967fa.accept_9_1_6_7_1_285 37 69 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 69 133 (Polychromatic418967fa.accept_10_6_9_3_1_935 36 69 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 69 133 (accept_3_3 35 69 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 69 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 69 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 133 (Polychromatic418967fa.accept_13_7_4_3_1_3064
  33 69 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 133 (accept_3_3 32
  69 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 133
  (Polychromatic418967fa.accept_9_4_6_7_1_286 31 69 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 69 133 (Polychromatic418967fa.accept_9_3_6_7_1_562 30 69 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 133 (accept_3_3 29 69 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 69 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 69 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 133 (Polychromatic418967fa.accept_12_3_9_1_1_290
  27 69 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 133 (accept_3_3 26
  69 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 133
  (Polychromatic418967fa.accept_13_12_4_3_1_1528 25 69 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 69 133 (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 69 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 133 (accept_3_3 23 69 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 69 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 69 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 133 (Polychromatic418967fa.accept_9_3_6_7_1_562 21
  69 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 133 (accept_3_3 20 69
  133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 133
  (Polychromatic418967fa.accept_9_1_6_7_1_285 19 69 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 69 133 (Polychromatic418967fa.accept_15_3_9_13_1_1681 18 69 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 133 (accept_3_3 17 69 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 69 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 69 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 133 (Polychromatic418967fa.accept_12_3_9_1_1_290
  15 69 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 133 (accept_3_3 14
  69 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 133
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 69 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 69 133 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 69 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 133 (accept_3_3 11 69 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 69 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 69 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 133 (Polychromatic418967fa.accept_21_9_6_7_1_6749 9
  69 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 133 (accept_3_3 8 69 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 133 (Polychromatic418967fa.accept_13_7_4_3_1_3064 7
  69 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69 133
  (Polychromatic418967fa.accept_10_6_9_3_1_935 6 69 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 133 (accept_3_3 5 69 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69
  133 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 69 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 69 133 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 69 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 133 (accept_3_3 2 69 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 69 133 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 69 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  133))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 68 133 (Eq.refl Bool.true)
  (allA_of_3_1 66 68 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 67 133 (allA_succ_of_accept 66 67 133
  (Polychromatic418967fa.accept_4_2_3_1_1_2 66 67 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 133 (accept_3_3 65 67 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 67 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 133 (Polychromatic418967fa.accept_13_11_2_3_1_883 63 67 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 133 (accept_3_3 62 67 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 133 (Polychromatic418967fa.accept_13_9_2_3_1_3027 61 67 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 133
  (Polychromatic418967fa.accept_9_6_4_7_1_300 60 67 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 133 (accept_3_3 59 67 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 67 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 133 (Polychromatic418967fa.accept_9_3_4_7_1_89 57 67 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 133 (accept_3_3 56 67 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 67 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 133
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 67 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 133 (accept_3_3 53 67 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 133 (Polychromatic418967fa.accept_14_10_11_7_1_1955 52 67 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 133 (Polychromatic418967fa.accept_9_6_4_7_1_300 51 67 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 133 (accept_3_3 50 67 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 133 (Polychromatic418967fa.accept_13_10_2_3_1_3025 49 67 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 133
  (Polychromatic418967fa.accept_9_3_4_7_1_89 48 67 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 133 (accept_3_3 47 67 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 67 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 133 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 67 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 133 (accept_3_3 44 67 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 133 (Polychromatic418967fa.accept_21_1_4_7_1_3689 43 67 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 133
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 67 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 133 (accept_3_3 41 67 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 133 (Polychromatic418967fa.accept_13_1_2_3_1_911 40 67 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 133 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 67 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 133 (accept_3_3 38 67 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 67 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 133
  (Polychromatic418967fa.accept_10_6_7_3_1_547 36 67 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 133 (accept_3_3 35 67 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 67 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 133 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 67 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 133 (accept_3_3 32 67 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 133 (Polychromatic418967fa.accept_13_5_2_3_1_1526 31 67 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 133
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 67 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 133 (accept_3_3 29 67 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 67 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 133 (Polychromatic418967fa.accept_13_1_2_3_1_911 27 67 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 133 (accept_3_3 26 67 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 133 (Polychromatic418967fa.accept_10_5_7_3_1_561 25 67 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 133
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 67 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 133 (accept_3_3 23 67 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 67 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 133 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 67 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 133 (accept_3_3 20 67 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 67 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 133
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 67 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 133 (accept_3_3 17 67 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 133 (Polychromatic418967fa.accept_10_6_7_3_1_547 16 67 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 133 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 67 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 133 (accept_3_3 14 67 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 133 (Polychromatic418967fa.accept_21_13_4_7_1_5190 13 67 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 133
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 67 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 133 (accept_3_3 11 67 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 67 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 133 (Polychromatic418967fa.accept_13_9_2_3_1_3027 9 67 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 133 (accept_3_3 8 67 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 133 (Polychromatic418967fa.accept_24_7_19_13_1_6703 7 67 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 133
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 67 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 133 (accept_3_3 5 67 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  133 (Polychromatic418967fa.accept_10_4_7_3_1_54 4 67 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 67 133 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 67 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 133 (accept_3_3 2 67 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 67 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 67 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  133))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 133 (allA_succ_of_accept 65 66
  133 (accept_3_3 65 66 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 66 133
  (Polychromatic418967fa.accept_9_1_3_7_1_6 64 66 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 66 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 66 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 66 133 (accept_3_3 62 66 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 66 133 (Polychromatic418967fa.accept_16_13_2_5_1_3336 61 66 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 66 133
  (Polychromatic418967fa.accept_9_6_3_7_1_580 60 66 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 66 133 (accept_3_3 59 66 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  66 133 (Polychromatic418967fa.accept_9_4_3_7_1_296 58 66 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 66 133 (Polychromatic418967fa.accept_10_7_6_3_1_927 57 66 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 66 133 (accept_3_3 56 66 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 66 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 66 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 66 133
  (Polychromatic418967fa.accept_13_2_1_3_1_419 54 66 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 66 133 (accept_3_3 53 66 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  66 133 (Polychromatic418967fa.accept_15_7_6_13_1_936 52 66 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 66 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 66 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 66 133 (accept_3_3 50 66 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 133 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 66 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 66 133
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 48 66 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 66 133 (accept_3_3 47 66 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  66 133 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 66 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 66 133 (Polychromatic418967fa.accept_13_6_1_3_1_1522 45 66 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 66 133 (accept_3_3 44 66 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 66 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 66 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 66 133
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 66 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 66 133 (accept_3_3 41 66 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  66 133 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 66 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 66 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 66 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 66 133 (accept_3_3 38 66 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 66 133 (Polychromatic418967fa.accept_9_1_3_7_1_6 37 66 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 66 133
  (Polychromatic418967fa.accept_21_15_3_7_1_6748 36 66 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 66 133 (accept_3_3 35 66 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  66 133 (Polychromatic418967fa.accept_15_4_6_13_1_956 34 66 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 66 133 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 66 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 66 133 (accept_3_3 32 66 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 66 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 66 133
  (Polychromatic418967fa.accept_13_4_1_3_1_3058 30 66 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 66 133 (accept_3_3 29 66 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  66 133 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 66 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 66 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 66 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 66 133 (accept_3_3 26 66 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 133 (Polychromatic418967fa.accept_14_11_10_7_1_1948 25 66 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 66 133
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 66 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 66 133 (accept_3_3 23 66 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  66 133 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 66 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 66 133 (Polychromatic418967fa.accept_18_3_12_7_1_6728 21 66 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 66 133 (accept_3_3 20 66 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 66 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 66 133
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 66 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 66 133 (accept_3_3 17 66 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  66 133 (Polychromatic418967fa.accept_17_16_15_14_1_6747 16 66 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 66 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 66 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 66 133 (accept_3_3 14 66 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 133 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 66 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 66 133
  (Polychromatic418967fa.accept_17_12_15_14_1_6746 12 66 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 66 133 (accept_3_3 11 66 133 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 66 133 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 66 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 66 133 (Polychromatic418967fa.accept_10_9_6_3_1_545 9 66 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 66 133 (accept_3_3 8 66 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 66
  133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 66 133
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 66 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 66 133 (accept_3_3 5 66 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66
  133 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 66 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 66 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 66 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 66 133 (accept_3_3 2 66 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 66 133 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 66 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  133)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 133 (allA_of_3_1 65 65 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 64 133 (allA_succ_of_accept 63 64 133
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 64 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 64 133 (accept_3_3 62 64 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  64 133 (Polychromatic418967fa.accept_13_9_12_3_1_907 61 64 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 64 133 (Polychromatic418967fa.accept_9_6_1_7_1_577 60 64 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 64 133 (accept_3_3 59 64 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 64 133 (Polychromatic418967fa.accept_9_4_1_7_1_293 58 64 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 64 133
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 64 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 64 133 (accept_3_3 56 64 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  64 133 (Polychromatic418967fa.accept_14_13_8_7_1_1224 55 64 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 64 133 (Polychromatic418967fa.accept_11_10_9_1_1_2186 54 64 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 64 133 (accept_3_3 53 64 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 64 133 (Polychromatic418967fa.accept_17_1_13_14_1_478 52 64
  133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 64 133
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 64 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 64 133 (accept_3_3 50 64 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  64 133 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 64 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 64 133 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 64 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 64 133 (accept_3_3 47 64 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 64 133 (Polychromatic418967fa.accept_12_10_4_1_1_1843 46 64 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 64 133
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 64 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 64 133 (accept_3_3 44 64 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  64 133 (Polychromatic418967fa.accept_11_10_9_1_1_2186 43 64 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 64 133 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 64 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 64 133 (accept_3_3 41 64 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 64 133 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 64 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 64 133
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 64 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 64 133 (accept_3_3 38 64 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  64 133 (Polychromatic418967fa.accept_10_7_4_3_1_560 37 64 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 64 133 (Polychromatic418967fa.accept_15_6_4_13_1_403 36 64 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 64 133 (accept_3_3 35 64 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 64 133 (Polychromatic418967fa.accept_12_10_4_1_1_1843 34 64 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 64 133
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 64 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 64 133 (accept_3_3 32 64 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  64 133 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 64 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 64 133 (Polychromatic418967fa.accept_9_3_1_7_1_97 30 64 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 64 133 (accept_3_3 29 64 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 64 133 (Polychromatic418967fa.accept_13_2_12_3_1_415 28 64 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 64 133
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 64 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 64 133 (accept_3_3 26 64 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  64 133 (Polychromatic418967fa.accept_15_10_4_13_1_4506 25 64 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 64 133 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 64 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 64 133 (accept_3_3 23 64 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 64 133 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 64 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 64 133
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 64 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 64 133 (accept_3_3 20 64 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  64 133 (Polychromatic418967fa.accept_10_9_4_3_1_539 19 64 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 64 133 (Polychromatic418967fa.accept_17_1_13_14_1_478 18 64 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 64 133 (accept_3_3 17 64 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 64 133 (Polychromatic418967fa.accept_21_16_1_7_1_6725 16 64
  133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 64 133
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 64 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 64 133 (accept_3_3 14 64 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  64 133 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 64 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 64 133 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 64 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 64 133 (accept_3_3 11 64 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 64 133 (Polychromatic418967fa.accept_11_10_9_1_1_2186 10 64 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 64 133
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 64 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 64 133 (accept_3_3 8 64 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 64
  133 (Polychromatic418967fa.accept_10_7_4_3_1_560 7 64 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 64 133 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 64 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 64 133 (accept_3_3 5 64 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 64 133 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 64 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 64 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 64
  133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 64 133 (accept_3_3 2 64 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 64 133 (Polychromatic418967fa.accept_14_1_8_7_1_1253 1
  64 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64
  133)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 133 (allA_succ_of_accept 62 63 133
  (accept_3_3 62 63 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 63 133
  (Polychromatic418967fa.accept_15_1_3_13_1_2548 61 63 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 63 133 (Polychromatic418967fa.accept_13_8_11_3_1_3053 60 63 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 63 133 (accept_3_3 59 63 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 63 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 63 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 133 (Polychromatic418967fa.accept_12_9_3_1_1_303
  57 63 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 63 133 7 8 9 19 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 63 133
  (Polychromatic418967fa.accept_15_10_3_13_1_4480 55 63 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 63 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 63 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 63 133 (accept_3_3 53 63 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 63 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 63 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 133
  (Polychromatic418967fa.accept_20_11_3_13_1_6745 51 63 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 63 133 (accept_3_3 50 63 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 63
  133 7 7 9 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48
  63 133 (Polychromatic418967fa.accept_11_4_8_1_1_1047 48 63 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 63 133 (accept_3_3 47 63 133 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 63 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 63 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 133 (Polychromatic418967fa.accept_12_9_3_1_1_303 45 63 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 133 (accept_3_3 44 63 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 63 133
  (Polychromatic418967fa.accept_17_9_12_14_1_5423 43 63 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 63 133 7 6 9 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 63 133 (accept_3_3 41 63 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  63 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 63 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 63 133 (Polychromatic418967fa.accept_15_9_3_13_1_1686 39 63 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 133 (accept_3_3 38 63 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 133 (Polychromatic418967fa.accept_11_4_8_1_1_1047 37 63 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 63 133
  (Polychromatic418967fa.accept_13_10_11_3_1_1518 36 63 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 63 133 7 5 9 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 63 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 63 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 133 (Polychromatic418967fa.accept_12_9_3_1_1_303 33 63 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 133 (accept_3_3 32 63 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 133 (Polychromatic418967fa.accept_13_5_11_3_1_902
  31 63 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 63 133
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 63 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 63 133 (accept_3_3 29 63 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 63
  133 7 4 9 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  63 133 (Polychromatic418967fa.accept_13_1_11_3_1_901 27 63 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 63 133 (accept_3_3 26 63 133 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 133 (Polychromatic418967fa.accept_15_10_3_13_1_4480 25 63 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 63 133 (Polychromatic418967fa.accept_15_9_3_13_1_1686 24 63
  133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 133 (accept_3_3 23 63 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 22
  63 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 63 133 7 3 9 19 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 63 133 (accept_3_3 20
  63 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 133
  (Polychromatic418967fa.accept_23_19_17_18_1_6744 19 63 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 63 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 63 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 133 (accept_3_3 17 63 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 63 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 133
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 15 63 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 63 133 7 2 9 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 63 133 (Polychromatic418967fa.accept_28_13_7_21_1_6743 13 63 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 63 133 (Polychromatic418967fa.accept_15_12_3_13_1_4481 12 63
  133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 133 (accept_3_3 11 63 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 10
  63 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 133
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 63 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 63 133 (accept_3_3 8 63 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 63 133
  7 1 9 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 63 133
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 63 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 133 (accept_3_3 5 63 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63
  133 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 63 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 63 133 (Polychromatic418967fa.accept_18_3_9_7_1_1839 3 63 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 133 (accept_3_3 2 63 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 63 133 (Polychromatic418967fa.accept_13_1_11_3_1_901 1 63 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  133))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 133 (allA_of_3_1 62 62 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 61 133 (allA_succ_of_accept 60 61 133
  (Polychromatic418967fa.accept_11_5_6_1_1_988 60 61 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 133 (accept_3_3 59 61 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 133 (Polychromatic418967fa.accept_10_8_1_3_1_1374 58 61 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 133 (Polychromatic418967fa.accept_13_5_9_3_1_870 57 61 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 133 (accept_3_3 56 61 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 133 (Polychromatic418967fa.accept_15_10_1_13_1_2609 55 61 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 133
  (Polychromatic418967fa.accept_13_2_9_3_1_2212 54 61 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 133 (accept_3_3 53 61 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 133 (Polychromatic418967fa.accept_10_2_1_3_1_233 52 61 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 133 (Polychromatic418967fa.accept_11_7_6_1_1_2182 51 61 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 133 (accept_3_3 50 61 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 133 (Polychromatic418967fa.accept_11_5_6_1_1_988 49 61 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 133
  (Polychromatic418967fa.accept_10_8_1_3_1_1374 48 61 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 133 (accept_3_3 47 61 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 133 (Polychromatic418967fa.accept_13_7_9_3_1_1504 46 61 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 133 (Polychromatic418967fa.accept_13_6_9_3_1_915 45 61 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 133 (accept_3_3 44 61 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 133 (Polychromatic418967fa.accept_20_3_1_13_1_6742 43 61 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 133
  (Polychromatic418967fa.accept_10_2_1_3_1_233 42 61 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 133 (accept_3_3 41 61 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 133 (Polychromatic418967fa.accept_11_7_6_1_1_2182 40 61 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 133 (Polychromatic418967fa.accept_17_5_10_14_1_2083 39 61 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 133 (accept_3_3 38 61 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 133 (Polychromatic418967fa.accept_14_9_5_7_1_1251 37 61 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 133
  (Polychromatic418967fa.accept_21_15_19_7_1_6741 36 61 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 133 (accept_3_3 35 61 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 133 (Polychromatic418967fa.accept_13_8_9_3_1_2213 34 61 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 133 (Polychromatic418967fa.accept_13_7_9_3_1_1504 33 61 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 133 (accept_3_3 32 61 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 133 (Polychromatic418967fa.accept_13_5_9_3_1_870 31 61 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 133
  (Polychromatic418967fa.accept_14_2_5_7_1_3767 30 61 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 133 (accept_3_3 29 61 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 133 (Polychromatic418967fa.accept_10_8_1_3_1_1374 28 61 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 133 (Polychromatic418967fa.accept_11_5_6_1_1_988 27 61 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 133 (accept_3_3 26 61 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 133 (Polychromatic418967fa.accept_13_12_9_3_1_3047 25 61 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 133
  (Polychromatic418967fa.accept_16_8_13_5_1_1395 24 61 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 133 (accept_3_3 23 61 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 133 (Polychromatic418967fa.accept_10_2_1_3_1_233 22 61 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 133 (Polychromatic418967fa.accept_13_8_9_3_1_2213 21 61 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 133 (accept_3_3 20 61 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 133 (Polychromatic418967fa.accept_13_6_9_3_1_915 19 61 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 133
  (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 61 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 133 (accept_3_3 17 61 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 133 (Polychromatic418967fa.accept_11_5_6_1_1_988 16 61 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 133 (Polychromatic418967fa.accept_13_2_9_3_1_2212 15 61 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 133 (accept_3_3 14 61 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 133 (Polychromatic418967fa.accept_17_13_10_14_1_4211 13 61 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 133
  (Polychromatic418967fa.accept_10_2_1_3_1_233 12 61 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 133 (accept_3_3 11 61 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 133 (Polychromatic418967fa.accept_15_10_1_13_1_2609 10 61 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 133 (Polychromatic418967fa.accept_14_9_5_7_1_1251 9 61 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 133 (accept_3_3 8 61 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 133 (Polychromatic418967fa.accept_11_7_6_1_1_2182 7 61 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 133
  (Polychromatic418967fa.accept_13_6_9_3_1_915 6 61 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 133 (accept_3_3 5 61 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  133 (Polychromatic418967fa.accept_21_4_19_7_1_5142 4 61 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 61 133 (Polychromatic418967fa.accept_15_3_1_13_1_1672 3 61 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 133 (accept_3_3 2 61 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 61 133 (Polychromatic418967fa.accept_16_1_13_5_1_2280 1 61 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61
  133))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 60 133 (allA_succ_of_accept 59 60 133
  (accept_3_3 59 60 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 60 133
  (Polychromatic418967fa.accept_9_4_6_7_1_286 58 60 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 60 133 (Polychromatic418967fa.accept_8_1_4_5_1_48 57 60 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 60 133 (accept_3_3 56 60 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 60 133 (Polychromatic418967fa.accept_9_1_6_7_1_285 55 60 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 60 133
  (Polychromatic418967fa.accept_21_12_18_7_1_6740 54 60 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 60 133 (accept_3_3 53 60 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  60 133 (Polychromatic418967fa.accept_14_10_4_7_1_1214 52 60 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 60 133 (Polychromatic418967fa.accept_21_9_18_7_1_5180 51 60 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 60 133 (accept_3_3 50 60 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 60 133 (Polychromatic418967fa.accept_8_1_4_5_1_48 49 60 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 60 133
  (Polychromatic418967fa.accept_9_3_6_7_1_562 48 60 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 60 133 (accept_3_3 47 60 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  60 133 (Polychromatic418967fa.accept_9_1_6_7_1_285 46 60 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 60 133 (Polychromatic418967fa.accept_14_3_4_7_1_175 45 60 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 60 133 (accept_3_3 44 60 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 133 (Polychromatic418967fa.accept_22_21_16_1_1_6739 43 60 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 60 133
  (Polychromatic418967fa.accept_16_10_12_5_1_2254 42 60 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 60 133 (accept_3_3 41 60 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  60 133 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 60 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 60 133 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 60 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 60 133 (accept_3_3 38 60 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 133 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 60 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 60 133
  (Polychromatic418967fa.accept_16_4_12_5_1_2287 36 60 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 60 133 (accept_3_3 35 60 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  60 133 (Polychromatic418967fa.accept_21_13_18_7_1_1216 34 60 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 60 133 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 60 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 60 133 (accept_3_3 32 60 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 133 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 60 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 60 133
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 60 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 60 133 (accept_3_3 29 60 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  60 133 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 60 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 60 133 (Polychromatic418967fa.accept_18_9_6_7_1_6719 27 60 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 60 133 (accept_3_3 26 60 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 60 133 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 60 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 60 133
  (Polychromatic418967fa.accept_13_11_8_3_1_3016 24 60 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 60 133 (accept_3_3 23 60 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  60 133 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 60 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 60 133 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 60 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 60 133 (accept_3_3 20 60 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 133 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 60 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 60 133
  (Polychromatic418967fa.accept_13_5_8_3_1_1535 18 60 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 60 133 (accept_3_3 17 60 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  60 133 (Polychromatic418967fa.accept_23_16_14_18_1_6738 16 60 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 60 133 (Polychromatic418967fa.accept_21_15_18_7_1_5161 15 60 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 60 133 (accept_3_3 14 60 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 133 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 60 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 60 133
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 60 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 60 133 (accept_3_3 11 60 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  60 133 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 60 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 60 133 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 60 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 60 133 (accept_3_3 8 60 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 133 (Polychromatic418967fa.accept_13_7_8_3_1_1533 7 60 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 60 133
  (Polychromatic418967fa.accept_11_6_5_1_1_586 6 60 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 60 133 (accept_3_3 5 60 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 60
  133 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 60 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 60 133 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 60 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 60 133 (accept_3_3 2 60 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 60 133 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 60 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60 133))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 59 133 (allA_of_3_1 59 59 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 58 133
  (allA_succ_of_accept 57 58 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 58 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 58 133 (accept_3_3 56 58 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 58 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 58 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 58 133 (Polychromatic418967fa.accept_14_12_2_7_1_1243
  54 58 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 58 133 (accept_3_3 53
  58 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 58 133
  (Polychromatic418967fa.accept_12_4_10_1_1_706 52 58 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 58 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 58 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 58 133 (accept_3_3 50 58 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 58 133 (Polychromatic418967fa.accept_13_10_6_3_1_1515 49 58 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 58 133
  (Polychromatic418967fa.accept_9_3_4_7_1_89 48 58 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 58 133 (accept_3_3 47 58 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  58 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 58 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 58 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 58 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 58 133 (accept_3_3 44 58 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 58 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 58 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 58 133
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 58 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 58 133 (accept_3_3 41 58 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  58 133 (Polychromatic418967fa.accept_12_4_10_1_1_706 40 58 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 58 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 58 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 58 133 (accept_3_3 38 58 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 58 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 58 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 58 133
  (Polychromatic418967fa.accept_10_6_8_3_1_930 36 58 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 58 133 (accept_3_3 35 58 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  58 133 (Polychromatic418967fa.accept_18_16_4_7_1_2927 34 58 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 58 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 58 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 58 133 (accept_3_3 32 58 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 58 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 58 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 58 133
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 58 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 58 133 (accept_3_3 29 58 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  58 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 58 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 58 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 58 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 58 133 (accept_3_3 26 58 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 58 133 (Polychromatic418967fa.accept_10_5_8_3_1_229 25 58 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 58 133
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 58 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 58 133 (accept_3_3 23 58 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  58 133 (Polychromatic418967fa.accept_13_9_6_3_1_1514 22 58 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 58 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 58 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 58 133 (accept_3_3 20 58 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 58 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 58 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 58 133
  (Polychromatic418967fa.accept_13_5_6_3_1_868 18 58 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 58 133 (accept_3_3 17 58 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  58 133 (Polychromatic418967fa.accept_10_6_8_3_1_930 16 58 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 58 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 58 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 58 133 (accept_3_3 14 58 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 58 133 (Polychromatic418967fa.accept_11_2_3_1_1_244 13 58 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 58 133
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 58 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 58 133 (accept_3_3 11 58 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  58 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 58 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 58 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 58 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 58 133 (accept_3_3 8 58 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 58 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 58 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 58 133
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 58 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 58 133 (accept_3_3 5 58 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 58
  133 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 58 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 58 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 58 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 58 133 (accept_3_3 2 58 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 58 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 58 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  133)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 133 (allA_succ_of_accept 56 57 133
  (accept_3_3 56 57 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 133
  (Polychromatic418967fa.accept_9_1_3_7_1_6 55 57 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 57 133 (Polychromatic418967fa.accept_10_4_7_3_1_54 54 57 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 133 (accept_3_3 53 57 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 57 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 57 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 133 (Polychromatic418967fa.accept_9_6_3_7_1_580 51
  57 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 133 (accept_3_3 50 57
  133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 133
  (Polychromatic418967fa.accept_9_4_3_7_1_296 49 57 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 57 133 (Polychromatic418967fa.accept_13_9_5_3_1_428 48 57 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 57 133 (accept_3_3 47 57 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 57 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 57 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 133 (Polychromatic418967fa.accept_10_5_7_3_1_561
  45 57 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 133 (accept_3_3 44
  57 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 133
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 43 57 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 57 133 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 57 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 57 133 (accept_3_3 41 57 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 57 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 57 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 133 (Polychromatic418967fa.accept_12_3_9_1_1_290
  39 57 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 57 133 19 2 3 7 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 57 133
  (Polychromatic418967fa.accept_9_1_3_7_1_6 37 57 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 57 133 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 57 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 57 133 (accept_3_3 35 57 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 57 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 57 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 133 (Polychromatic418967fa.accept_9_6_3_7_1_580 33
  57 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 133 (accept_3_3 32 57
  133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 133
  (Polychromatic418967fa.accept_9_4_3_7_1_296 31 57 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 57 133 (Polychromatic418967fa.accept_16_14_9_5_1_4388 30 57 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 57 133 (accept_3_3 29 57 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 57 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 57 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 133 (Polychromatic418967fa.accept_12_3_9_1_1_290
  27 57 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 133 (accept_3_3 26
  57 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 133
  (Polychromatic418967fa.accept_10_5_7_3_1_561 25 57 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 57 133 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 57 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 57 133 (accept_3_3 23 57 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 57 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 57 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 133 (Polychromatic418967fa.accept_11_10_2_1_1_1036
  21 57 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 133 (accept_3_3 20
  57 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 19 57 133 19 1 3 7 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 18 57 133
  (Polychromatic418967fa.accept_15_3_12_13_1_2549 18 57 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 57 133 (accept_3_3 17 57 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  57 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 57 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 57 133 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 57 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 133 (accept_3_3 14 57 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 133 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 57 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 57 133
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 57 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 57 133 (accept_3_3 11 57 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  57 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 57 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 57 133 (Polychromatic418967fa.accept_13_9_5_3_1_428 9 57 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 133 (accept_3_3 8 57 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 133 (Polychromatic418967fa.accept_17_7_6_14_1_6737 7 57 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 133
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 57 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 133 (accept_3_3 5 57 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57
  133 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 57 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 57 133 (Polychromatic418967fa.accept_11_3_2_1_1_994 3 57 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 133 (accept_3_3 2 57 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 57 133 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 57 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 133)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 133 (allA_of_3_1 56 56 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 55 133
  (allA_succ_of_accept 54 55 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 55 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 133 (accept_3_3 53 55 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 55 133 (Polychromatic418967fa.accept_10_2_5_3_1_1408 52 55 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 133 (Polychromatic418967fa.accept_9_6_1_7_1_577 51
  55 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 55 133 (accept_3_3 50 55
  133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 55 133
  (Polychromatic418967fa.accept_9_4_1_7_1_293 49 55 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 55 133 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 55 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 133 (accept_3_3 47 55 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 55 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 55 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 55 133
  (Polychromatic418967fa.accept_20_5_15_13_1_5235 45 55 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 55 133 (accept_3_3 44 55 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  55 133 (Polychromatic418967fa.accept_14_1_13_7_1_1205 43 55 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 55 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 55 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 55 133 (accept_3_3 41 55 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 55 133 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 55 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 55 133
  (Polychromatic418967fa.accept_9_3_1_7_1_97 39 55 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 55 133 (accept_3_3 38 55 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  55 133 (Polychromatic418967fa.accept_10_7_5_3_1_542 37 55 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 55 133 (Polychromatic418967fa.accept_14_8_13_7_1_2798 36 55 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 55 133 (accept_3_3 35 55 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 55 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 55 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 55 133
  (Polychromatic418967fa.accept_9_6_1_7_1_577 33 55 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 55 133 (accept_3_3 32 55 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  55 133 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 55 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 55 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 55 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 55 133 (accept_3_3 29 55 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 133 (Polychromatic418967fa.accept_10_8_5_3_1_543 28 55 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 133
  (Polychromatic418967fa.accept_10_7_5_3_1_542 27 55 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 55 133 (accept_3_3 26 55 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  55 133 (Polychromatic418967fa.accept_20_5_15_13_1_5235 25 55 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 55 133 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 55 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 55 133 (accept_3_3 23 55 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 55 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 55 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 133
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 55 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 55 133 (accept_3_3 20 55 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  55 133 (Polychromatic418967fa.accept_15_4_10_13_1_2565 19 55 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 55 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 55 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 133 (accept_3_3 17 55 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 55 133 (Polychromatic418967fa.accept_15_1_10_13_1_939 16 55 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 55 133
  (Polychromatic418967fa.accept_9_6_1_7_1_577 15 55 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 55 133 (accept_3_3 14 55 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  55 133 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 55 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 55 133 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 55 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 55 133 (accept_3_3 11 55 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 55 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 55 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 55 133
  (Polychromatic418967fa.accept_17_9_4_14_1_4302 9 55 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 55 133 (accept_3_3 8 55 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55
  133 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 55 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 55 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 55 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 55 133 (accept_3_3 5 55 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 55 133 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 55 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 133 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 55
  133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 133 (accept_3_3 2 55 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55 133 (Polychromatic418967fa.accept_14_1_13_7_1_1205
  1 55 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55
  133))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 54 133 (allA_succ_of_accept 53 54 133
  (accept_3_3 53 54 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 54 133
  (Polychromatic418967fa.accept_15_7_9_13_1_3451 52 54 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 54 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 54 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 54 133 (accept_3_3 50 54 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 54 133 (Polychromatic418967fa.accept_10_9_4_3_1_539 49 54 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 133 (Polychromatic418967fa.accept_13_9_2_3_1_3027
  48 54 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 54 133 (accept_3_3 47
  54 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 54 133
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 46 54 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 54 133 (Polychromatic418967fa.accept_17_11_3_14_1_6736 45 54 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 54 133 (accept_3_3 44 54 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 54 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 54 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 133 (Polychromatic418967fa.accept_11_9_10_1_1_581
  42 54 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 54 133 (accept_3_3 41
  54 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 54 133
  (Polychromatic418967fa.accept_13_1_2_3_1_911 40 54 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 54 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 54 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 54 133 (accept_3_3 38 54 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 54 133 (Polychromatic418967fa.accept_10_7_4_3_1_560 37 54 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 54 133 (Polychromatic418967fa.accept_13_10_2_3_1_3025
  36 54 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 54 133 (accept_3_3 35
  54 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 54 133
  (Polychromatic418967fa.accept_15_4_9_13_1_2582 34 54 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 54 133 (Polychromatic418967fa.accept_14_5_12_7_1_2767 33 54 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 54 133 (accept_3_3 32 54 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 54 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 54 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 54 133 (Polychromatic418967fa.accept_14_2_12_7_1_617
  30 54 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 54 133 (accept_3_3 29
  54 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 54 133
  (Polychromatic418967fa.accept_17_11_3_14_1_6736 28 54 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 54 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 54 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 133 (accept_3_3 26 54 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 54 133 (Polychromatic418967fa.accept_13_12_2_3_1_1527 25 54 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 54 133
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 24 54 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 54 133 (accept_3_3 23 54 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  54 133 (Polychromatic418967fa.accept_13_9_2_3_1_3027 22 54 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 54 133 (Polychromatic418967fa.accept_20_1_14_13_1_6735 21 54 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 133 (accept_3_3 20 54 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 54 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 54 133
  (Polychromatic418967fa.accept_13_5_2_3_1_1526 18 54 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 54 133 (accept_3_3 17 54 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  54 133 (Polychromatic418967fa.accept_14_2_12_7_1_617 16 54 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 54 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 54 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 133 (accept_3_3 14 54 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 133 (Polychromatic418967fa.accept_11_2_10_1_1_1017 13 54 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 54 133
  (Polychromatic418967fa.accept_13_12_2_3_1_1527 12 54 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 54 133 (accept_3_3 11 54 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  54 133 (Polychromatic418967fa.accept_13_10_2_3_1_3025 10 54 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 54 133 (Polychromatic418967fa.accept_10_9_4_3_1_539 9 54 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 133 (accept_3_3 8 54 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 54 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54 133
  (Polychromatic418967fa.accept_17_6_3_14_1_2078 6 54 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 54 133 (accept_3_3 5 54 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54
  133 (Polychromatic418967fa.accept_15_4_9_13_1_2582 4 54 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 54 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 54 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 133 (accept_3_3 2 54 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 133 (Polychromatic418967fa.accept_13_1_2_3_1_911 1 54 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  133)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 133 (allA_of_3_1 53 53 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 52 133 (allA_succ_of_accept 51 52 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 52
  133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 52 133 (accept_3_3 50 52 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 52 133 (Polychromatic418967fa.accept_8_1_4_5_1_48 49
  52 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 133
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 48 52 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 52 133 (accept_3_3 47 52 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  52 133 (Polychromatic418967fa.accept_12_10_4_1_1_1843 46 52 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 52 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 52 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 52 133 (accept_3_3 44 52 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 52 133 (Polychromatic418967fa.accept_20_3_12_13_1_3836 43 52 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 52 133
  (Polychromatic418967fa.accept_22_20_8_1_1_6734 42 52 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 52 133 (accept_3_3 41 52 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  52 133 (Polychromatic418967fa.accept_16_8_4_5_1_4379 40 52 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 52 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 52 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 52 133 (accept_3_3 38 52 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 52 133 (Polychromatic418967fa.accept_11_4_8_1_1_1047 37 52 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 52 133
  (Polychromatic418967fa.accept_15_6_7_13_1_1666 36 52 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 52 133 (accept_3_3 35 52 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  52 133 (Polychromatic418967fa.accept_12_10_4_1_1_1843 34 52 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 52 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 52 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 52 133 (accept_3_3 32 52 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 52 133 (Polychromatic418967fa.accept_10_1_2_3_1_1910 31 52 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 52 133
  (Polychromatic418967fa.accept_17_13_1_14_1_1149 30 52 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 52 133 (accept_3_3 29 52 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  52 133 (Polychromatic418967fa.accept_16_12_4_5_1_2273 28 52 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 52 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 52 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 52 133 (accept_3_3 26 52 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 52 133 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 52 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 52 133
  (Polychromatic418967fa.accept_15_9_7_13_1_1664 24 52 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 52 133 (accept_3_3 23 52 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  52 133 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 52 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 52 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 52 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 52 133 (accept_3_3 20 52 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 52 133 (Polychromatic418967fa.accept_18_1_16_7_1_2897 19 52 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 52 133
  (Polychromatic418967fa.accept_14_4_10_7_1_1946 18 52 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 52 133 (accept_3_3 17 52 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  52 133 (Polychromatic418967fa.accept_21_16_10_7_1_3782 16 52 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 52 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 52 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 52 133 (accept_3_3 14 52 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 52 133 (Polychromatic418967fa.accept_17_13_1_14_1_1149 13 52 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 52 133
  (Polychromatic418967fa.accept_16_12_4_5_1_2273 12 52 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 52 133 (accept_3_3 11 52 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  52 133 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 52 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 52 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 52 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 52 133 (accept_3_3 8 52 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 52 133 (Polychromatic418967fa.accept_22_7_8_1_1_6733 7 52 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 52 133
  (Polychromatic418967fa.accept_15_6_7_13_1_1666 6 52 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 52 133 (accept_3_3 5 52 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 52
  133 (Polychromatic418967fa.accept_11_4_8_1_1_1047 4 52 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 52 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 52 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 52 133 (accept_3_3 2 52 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 52 133 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 52 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52
  133)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 133 (allA_succ_of_accept 50 51 133 (accept_3_3
  50 51 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 133
  (Polychromatic418967fa.accept_9_4_6_7_1_286 49 51 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 51 133 (Polychromatic418967fa.accept_9_3_6_7_1_562 48 51 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 133 (accept_3_3 47 51 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 51 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 51 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 133 (Polychromatic418967fa.accept_12_9_3_1_1_303
  45 51 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 133 (accept_3_3 44
  51 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 133
  (Polychromatic418967fa.accept_13_4_12_3_1_2999 43 51 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 51 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 51 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 133 (accept_3_3 41 51 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 51 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 51 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 133 (Polychromatic418967fa.accept_9_3_6_7_1_562 39
  51 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 133 (accept_3_3 38 51
  133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 133
  (Polychromatic418967fa.accept_9_1_6_7_1_285 37 51 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 51 133 (Polychromatic418967fa.accept_21_15_9_7_1_3780 36 51 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 51 133 (accept_3_3 35 51 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 51 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 51 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 133 (Polychromatic418967fa.accept_12_9_3_1_1_303
  33 51 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 133 (accept_3_3 32
  51 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 133
  (Polychromatic418967fa.accept_9_4_6_7_1_286 31 51 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 51 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 51 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 133 (accept_3_3 29 51 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 51 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 51 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 133 (Polychromatic418967fa.accept_21_6_9_7_1_3752
  27 51 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 133 (accept_3_3 26
  51 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 133
  (Polychromatic418967fa.accept_23_2_5_18_1_6732 25 51 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 51 133 (Polychromatic418967fa.accept_16_8_3_5_1_5512 24 51 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 51 133 (accept_3_3 23 51 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 51 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 51 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 133 (Polychromatic418967fa.accept_9_3_6_7_1_562 21
  51 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 133 (accept_3_3 20 51
  133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 133
  (Polychromatic418967fa.accept_9_1_6_7_1_285 19 51 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 51 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 51 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 51 133 (accept_3_3 17 51 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 51 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 51 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 133 (Polychromatic418967fa.accept_13_2_12_3_1_415
  15 51 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 133 (accept_3_3 14
  51 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 133
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 51 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 51 133 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 51 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 133 (accept_3_3 11 51 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 51 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 51 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 133 (Polychromatic418967fa.accept_12_9_3_1_1_303 9
  51 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 133 (accept_3_3 8 51 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 133 (Polychromatic418967fa.accept_15_7_6_13_1_936 7
  51 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51 133
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 51 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 133 (accept_3_3 5 51 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51
  133 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 51 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 51 133 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 51 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 133 (accept_3_3 2 51 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 51 133 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 51 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 133)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 133 (allA_of_3_1 50 50 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 49 133
  (allA_succ_of_accept 48 49 133 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 49 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 133 (accept_3_3 47 49 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 49 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 49 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 133 (Polychromatic418967fa.accept_13_6_10_3_1_897
  45 49 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 133 (accept_3_3 44
  49 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 133
  (Polychromatic418967fa.accept_22_21_5_1_1_6731 43 49 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 49 133 7 6 7 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 49 133 (accept_3_3 41 49 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  49 133 (Polychromatic418967fa.accept_15_10_4_13_1_4506 40 49 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 49 133 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 49 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 133 (accept_3_3 38 49 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 49 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 49 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 133
  (Polychromatic418967fa.accept_8_4_1_5_1_186 36 49 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 49 133 7 5 7 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 49 133 (Polychromatic418967fa.accept_10_4_9_3_1_1907 34 49 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 133 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 49 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 133 (accept_3_3 32 49 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 133 (Polychromatic418967fa.accept_16_15_1_5_1_2265
  31 49 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 133
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 49 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 49 133 (accept_3_3 29 49 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 49
  133 7 4 7 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  49 133 (Polychromatic418967fa.accept_25_2_24_8_1_6730 27 49 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 49 133 (accept_3_3 26 49 133 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 49 133 (Polychromatic418967fa.accept_15_10_4_13_1_4506 25 49 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 133 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 49 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 133 (accept_3_3 23 49 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 133 (Polychromatic418967fa.accept_16_6_1_5_1_2242
  22 49 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 49 133 7 3 7 19 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 49 133 (accept_3_3 20
  49 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 133
  (Polychromatic418967fa.accept_9_1_4_7_1_7 19 49 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 49 133 (Polychromatic418967fa.accept_22_18_5_1_1_6729 18 49 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 133 (accept_3_3 17 49 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 49 133 (Polychromatic418967fa.accept_10_6_9_3_1_935 16 49 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 133 (Polychromatic418967fa.accept_9_6_4_7_1_300 15
  49 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 49 133 7 2 7 19 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 49 133
  (Polychromatic418967fa.accept_16_13_1_5_1_5469 13 49 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 49 133 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 49 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 133 (accept_3_3 11 49 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 49 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 49 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 133 (Polychromatic418967fa.accept_15_9_4_13_1_4482
  9 49 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 133 (accept_3_3 8 49
  133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 49 133 7 1 7 19 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 49 133
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 49 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 49 133 (accept_3_3 5 49 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49
  133 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 49 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 49 133 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 49 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 133 (accept_3_3 2 49 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 49 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 49 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 133))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  48 133 (allA_succ_of_accept 47 48 133 (accept_3_3 47 48 133 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 48 133 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 48 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 48 133 (Polychromatic418967fa.accept_10_5_8_3_1_229 45 48 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 48 133 (accept_3_3 44 48 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 133 (Polychromatic418967fa.accept_14_1_6_7_1_1936
  43 48 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 48 133
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 48 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 48 133 (accept_3_3 41 48 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  48 133 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 48 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 48 133 (Polychromatic418967fa.accept_15_9_3_13_1_1686 39 48 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 48 133 (accept_3_3 38 48 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 133 (Polychromatic418967fa.accept_9_1_3_7_1_6 37 48 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 133
  (Polychromatic418967fa.accept_10_6_8_3_1_930 36 48 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 48 133 (accept_3_3 35 48 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  48 133 (Polychromatic418967fa.accept_13_8_9_3_1_2213 34 48 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 48 133 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 48 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 48 133 (accept_3_3 32 48 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 133 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 48 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 133
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 30 48 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 48 133 (accept_3_3 29 48 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  48 133 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 48 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 48 133 (Polychromatic418967fa.accept_14_13_6_7_1_2013 27 48 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 48 133 (accept_3_3 26 48 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 133 (Polychromatic418967fa.accept_10_5_8_3_1_229 25 48 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 133
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 48 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 48 133 (accept_3_3 23 48 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  48 133 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 48 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 48 133 (Polychromatic418967fa.accept_10_1_8_3_1_947 21 48 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 48 133 (accept_3_3 20 48 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 133 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 48 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 48 133
  (Polychromatic418967fa.accept_13_5_9_3_1_870 18 48 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 48 133 (accept_3_3 17 48 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  48 133 (Polychromatic418967fa.accept_10_6_8_3_1_930 16 48 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 48 133 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 48 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 48 133 (accept_3_3 14 48 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 133 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 48 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 48 133
  (Polychromatic418967fa.accept_13_12_9_3_1_3047 12 48 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 48 133 (accept_3_3 11 48 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  48 133 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 48 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 48 133 (Polychromatic418967fa.accept_15_9_3_13_1_1686 9 48 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 48 133 (accept_3_3 8 48 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 133 (Polychromatic418967fa.accept_13_7_9_3_1_1504 7 48 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 133
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 48 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 48 133 (accept_3_3 5 48 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48
  133 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 48 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 48 133 (Polychromatic418967fa.accept_18_3_12_7_1_6728 3 48 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 48 133 (accept_3_3 2 48 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 48 133 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 48 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48 133)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  47 133 (allA_of_3_1 47 47 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 46 133 (allA_succ_of_accept 45 46
  133 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 46 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 46 133 (accept_3_3 44 46 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  46 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 46 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 46 133 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 46 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 133 (accept_3_3 41 46 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 46 133 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 46 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 46 133
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 46 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 46 133 (accept_3_3 38 46 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  46 133 (Polychromatic418967fa.accept_10_7_6_3_1_927 37 46 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 46 133 (Polychromatic418967fa.accept_11_3_2_1_1_994 36 46 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 46 133 (accept_3_3 35 46 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 46 133 (Polychromatic418967fa.accept_13_8_7_3_1_430 34 46 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 46 133
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 46 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 46 133 (accept_3_3 32 46 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  46 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 46 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 46 133 (Polychromatic418967fa.accept_9_3_1_7_1_97 30 46 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 46 133 (accept_3_3 29 46 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 46 133 (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 46 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 46 133
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 46 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 46 133 (accept_3_3 26 46 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  46 133 (Polychromatic418967fa.accept_11_3_2_1_1_994 25 46 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 46 133 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 46 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 133 (accept_3_3 23 46 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 46 133 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 46 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 46 133
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 46 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 46 133 (accept_3_3 20 46 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  46 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 46 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 46 133 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 46 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 133 (accept_3_3 17 46 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 46 133 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 46 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 46 133
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 46 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 46 133 (accept_3_3 14 46 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  46 133 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 46 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 46 133 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 46 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 46 133 (accept_3_3 11 46 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 46 133 (Polychromatic418967fa.accept_11_10_2_1_1_1036 10 46 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 46 133
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 46 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 46 133 (accept_3_3 8 46 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 46
  133 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 46 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 46 133 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 46 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 46 133 (accept_3_3 5 46 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 46 133 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 46 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 46 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 46
  133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 46 133 (accept_3_3 2 46 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 46 133 (Polychromatic418967fa.accept_13_1_7_3_1_1503 1
  46 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  133)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 133 (allA_succ_of_accept 44 45 133 (accept_3_3 44 45
  133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 133
  (Polychromatic418967fa.accept_21_1_3_7_1_3727 43 45 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 45 133 (Polychromatic418967fa.accept_10_2_5_3_1_1408 42 45 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 133 (accept_3_3 41 45 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 45 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 45 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 133 (Polychromatic418967fa.accept_12_3_9_1_1_290
  39 45 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 133 (accept_3_3 38
  45 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 133
  (Polychromatic418967fa.accept_10_7_5_3_1_542 37 45 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 45 133 (Polychromatic418967fa.accept_13_10_6_3_1_1515 36 45 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 45 133 (accept_3_3 35 45 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 45 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 45 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 133 (Polychromatic418967fa.accept_16_1_13_5_1_2280
  33 45 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 133 (accept_3_3 32
  45 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 133
  (Polychromatic418967fa.accept_13_5_6_3_1_868 31 45 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 45 133 (Polychromatic418967fa.accept_20_10_5_13_1_6727 30 45 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 45 133 (accept_3_3 29 45 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 45 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 45 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 133 (Polychromatic418967fa.accept_10_7_5_3_1_542
  27 45 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 133 (accept_3_3 26
  45 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 133
  (Polychromatic418967fa.accept_14_11_3_7_1_604 25 45 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 45 133 (Polychromatic418967fa.accept_14_10_3_7_1_1975 24 45 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 45 133 (accept_3_3 23 45 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 45 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 45 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 133 (Polychromatic418967fa.accept_18_3_9_7_1_1839
  21 45 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 133 (accept_3_3 20
  45 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 133
  (Polychromatic418967fa.accept_20_19_5_13_1_2593 19 45 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 45 133 (Polychromatic418967fa.accept_10_8_5_3_1_543 18 45 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 133 (accept_3_3 17 45 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 45 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 45 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 133 (Polychromatic418967fa.accept_12_3_9_1_1_290
  15 45 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 133 (accept_3_3 14
  45 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 133
  (Polychromatic418967fa.accept_25_13_20_8_1_6726 13 45 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 45 133 (Polychromatic418967fa.accept_10_2_5_3_1_1408 12 45 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 45 133 (accept_3_3 11 45 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 45 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 45 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 133 (Polychromatic418967fa.accept_13_9_6_3_1_1514 9
  45 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 133 (accept_3_3 8 45 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 133 (Polychromatic418967fa.accept_10_7_5_3_1_542 7
  45 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 133
  (Polychromatic418967fa.accept_18_6_9_7_1_2905 6 45 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 133 (accept_3_3 5 45 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45
  133 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 45 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 45 133 (Polychromatic418967fa.accept_12_3_9_1_1_290 3 45 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 133 (accept_3_3 2 45 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 45 133 (Polychromatic418967fa.accept_13_1_6_3_1_1547 1 45 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 133))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  133 (allA_of_3_1 44 44 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 43 133 (allA_succ_of_accept 42 43 133
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 43 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 133 (accept_3_3 41 43 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 133 (Polychromatic418967fa.accept_13_1_4_3_1_1545 40 43 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 133 (Polychromatic418967fa.accept_16_7_11_5_1_4402 39 43 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 133 (accept_3_3 38 43 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 133 (Polychromatic418967fa.accept_21_16_1_7_1_6725 37 43
  133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 133
  (Polychromatic418967fa.accept_14_8_1_7_1_3725 36 43 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 133 (accept_3_3 35 43 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 43 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 133 (Polychromatic418967fa.accept_13_7_4_3_1_3064 33 43 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 133 (accept_3_3 32 43 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 133 (Polychromatic418967fa.accept_11_9_10_1_1_581 31 43 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 133
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 43 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 133 (accept_3_3 29 43 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 133 (Polychromatic418967fa.accept_20_8_3_13_1_2590 28 43 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 133 (Polychromatic418967fa.accept_13_1_4_3_1_1545 27 43 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 133 (accept_3_3 26 43 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 133 (Polychromatic418967fa.accept_13_12_4_3_1_1528 25 43 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 133
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 24 43 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 133 (accept_3_3 23 43 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 43 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 133 (Polychromatic418967fa.accept_17_4_9_14_1_5406 21 43 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 133 (accept_3_3 20 43 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 133 (Polychromatic418967fa.accept_21_19_1_7_1_3724 19 43
  133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 133
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 43 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 133 (accept_3_3 17 43 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 133 (Polychromatic418967fa.accept_20_16_3_13_1_6724 16 43 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 133 (Polychromatic418967fa.accept_21_15_1_7_1_6723 15 43 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 133 (accept_3_3 14 43 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 133 (Polychromatic418967fa.accept_11_2_10_1_1_1017 13 43
  133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 133
  (Polychromatic418967fa.accept_13_12_4_3_1_1528 12 43 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 133 (accept_3_3 11 43 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 43 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 133 (Polychromatic418967fa.accept_11_9_10_1_1_581 9 43 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 133 (accept_3_3 8 43 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 133 (Polychromatic418967fa.accept_13_7_4_3_1_3064 7 43 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 133
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 43 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 133 (accept_3_3 5 43 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  133 (Polychromatic418967fa.accept_17_4_9_14_1_5406 4 43 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 43 133 (Polychromatic418967fa.accept_21_3_1_7_1_5187 3 43 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 133 (accept_3_3 2 43 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 43 133 (Polychromatic418967fa.accept_13_1_4_3_1_1545 1 43 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 133)))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 42 133 (allA_succ_of_accept 41 42 133 (accept_3_3 41 42 133 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 42 133 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 42 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 42 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 42 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 42 133 (accept_3_3 38 42 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 133 (Polychromatic418967fa.accept_9_1_6_7_1_285 37
  42 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 133
  (Polychromatic418967fa.accept_22_14_20_1_1_6722 36 42 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 42 133 7 5 6 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 42 133 (Polychromatic418967fa.accept_22_12_20_1_1_6721 34 42 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 42 133 (Polychromatic418967fa.accept_15_3_12_13_1_2549 33 42
  133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 42 133 (accept_3_3 32 42 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 31
  42 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 42 133
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 42 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 42 133 (accept_3_3 29 42 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42
  133 7 4 6 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  42 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 42 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 42 133 (accept_3_3 26 42 133 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 42 133 (Polychromatic418967fa.accept_10_5_2_3_1_239 25 42 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 133 (Polychromatic418967fa.accept_17_7_8_14_1_6720 24 42
  133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 42 133 (accept_3_3 23 42 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 42 133 (Polychromatic418967fa.accept_9_4_6_7_1_286 22
  42 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 42 133 7 3 6 19 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 42 133 (accept_3_3 20
  42 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 133
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 42 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 42 133 (Polychromatic418967fa.accept_15_3_12_13_1_2549 18 42 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 42 133 (accept_3_3 17 42 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 42 133 (Polychromatic418967fa.accept_15_1_12_13_1_944 16 42 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 42 133
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 42 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 42 133 7 2 6 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 42 133 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 42 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 133 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 42 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 42 133 (accept_3_3 11 42 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 42 133 (Polychromatic418967fa.accept_9_1_6_7_1_285 10
  42 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 42 133
  (Polychromatic418967fa.accept_18_9_6_7_1_6719 9 42 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 42 133 (accept_3_3 8 42 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 42 133
  7 1 6 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 42 133
  (Polychromatic418967fa.accept_17_6_8_14_1_6706 6 42 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 42 133 (accept_3_3 5 42 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42
  133 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 42 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 42 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 42 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 42 133 (accept_3_3 2 42 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 42 133 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 42 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42 133)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 133
  (allA_of_3_1 41 41 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 40 133 (allA_succ_of_accept 39 40 133
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 40 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 40 133 (accept_3_3 38 40 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  40 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 40 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 40 133 (Polychromatic418967fa.accept_16_4_8_5_1_3317 36 40 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 40 133 (accept_3_3 35 40 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 40 133 (Polychromatic418967fa.accept_12_10_4_1_1_1843 34 40 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 40 133
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 40 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 40 133 (accept_3_3 32 40 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  40 133 (Polychromatic418967fa.accept_13_5_1_3_1_878 31 40 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 40 133 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 40 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 40 133 (accept_3_3 29 40 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 40 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 40 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 40 133
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 40 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 40 133 (accept_3_3 26 40 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  40 133 (Polychromatic418967fa.accept_17_8_6_14_1_6718 25 40 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 40 133 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 40 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 40 133 (accept_3_3 23 40 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 40 133 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 40 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 40 133
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 40 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 40 133 (accept_3_3 20 40 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  40 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 40 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 40 133 (Polychromatic418967fa.accept_13_5_1_3_1_878 18 40 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 40 133 (accept_3_3 17 40 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 40 133 (Polychromatic418967fa.accept_14_2_12_7_1_617 16 40 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 40 133
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 40 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 40 133 (accept_3_3 14 40 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  40 133 (Polychromatic418967fa.accept_16_13_8_5_1_3298 13 40 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 40 133 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 40 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 40 133 (accept_3_3 11 40 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 40 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 40 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 40 133
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 40 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 40 133 (accept_3_3 8 40 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 40
  133 (Polychromatic418967fa.accept_13_7_1_3_1_1523 7 40 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 40 133 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 40 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 40 133 (accept_3_3 5 40 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 40 133 (Polychromatic418967fa.accept_13_4_1_3_1_3058 4 40 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 133
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 40 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 40 133 (accept_3_3 2 40 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40
  133 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 40 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 40 133)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 133 (allA_succ_of_accept 38 39 133 (accept_3_3
  38 39 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 133
  (Polychromatic418967fa.accept_9_1_3_7_1_6 37 39 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 39 133 (Polychromatic418967fa.accept_10_6_9_3_1_935 36 39 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 39 133 (accept_3_3 35 39 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 39 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 39 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 133 (Polychromatic418967fa.accept_9_6_3_7_1_580 33
  39 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 133 (accept_3_3 32 39
  133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 133
  (Polychromatic418967fa.accept_9_4_3_7_1_296 31 39 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 39 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 39 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 39 133 (accept_3_3 29 39 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 39 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 39 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 133 (Polychromatic418967fa.accept_11_5_6_1_1_988
  27 39 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 133 (accept_3_3 26
  39 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 133
  (Polychromatic418967fa.accept_20_5_19_13_1_6717 25 39 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 39 133 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 39 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 39 133 (accept_3_3 23 39 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 39 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 39 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 133 (Polychromatic418967fa.accept_12_9_3_1_1_303
  21 39 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 133 (accept_3_3 20
  39 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 133
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 39 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 39 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 39 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 39 133 (accept_3_3 17 39 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 39 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 39 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 133 (Polychromatic418967fa.accept_9_6_3_7_1_580 15
  39 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 133 (accept_3_3 14 39
  133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 133
  (Polychromatic418967fa.accept_9_4_3_7_1_296 13 39 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 39 133 (Polychromatic418967fa.accept_16_12_7_5_1_1412 12 39 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 39 133 (accept_3_3 11 39 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 39 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 39 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 133 (Polychromatic418967fa.accept_12_9_3_1_1_303 9
  39 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 133 (accept_3_3 8 39 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 133 (Polychromatic418967fa.accept_11_7_6_1_1_2182 7
  39 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39 133
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 39 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 133 (accept_3_3 5 39 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39
  133 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 39 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 39 133 (Polychromatic418967fa.accept_14_3_11_7_1_1260 3 39 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 133 (accept_3_3 2 39 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 39 133 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 39 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 133))))))))))))))))))))))))))))))))))))))) (allB_succ 38 133
  (allA_of_3_1 38 38 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 37 133 (allA_succ_of_accept 36 37 133
  (Polychromatic418967fa.accept_10_6_7_3_1_547 36 37 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 37 133 (accept_3_3 35 37 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  37 133 (Polychromatic418967fa.accept_10_4_7_3_1_54 34 37 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 37 133 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 37 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 133 (accept_3_3 32 37 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 133 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 37 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 133
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 37 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 133 (accept_3_3 29 37 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  37 133 (Polychromatic418967fa.accept_13_2_11_3_1_873 28 37 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 133 (Polychromatic418967fa.accept_13_1_11_3_1_901 27 37 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 133 (accept_3_3 26 37 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 133 (Polychromatic418967fa.accept_10_5_7_3_1_561 25 37 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 133
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 37 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 133 (accept_3_3 23 37 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 133 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 37 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 133 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 37 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 133 (accept_3_3 20 37 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 133 (Polychromatic418967fa.accept_11_8_4_1_1_1000 19 37 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 133
  (Polychromatic418967fa.accept_13_5_11_3_1_902 18 37 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 133 (accept_3_3 17 37 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  37 133 (Polychromatic418967fa.accept_10_6_7_3_1_547 16 37 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 133 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 37 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 133 (accept_3_3 14 37 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 133 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 37 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 133
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 37 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 133 (accept_3_3 11 37 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  37 133 (Polychromatic418967fa.accept_13_10_11_3_1_1518 10 37 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 133 (Polychromatic418967fa.accept_15_9_7_13_1_1664 9 37 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 133 (accept_3_3 8 37 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 133 (Polychromatic418967fa.accept_13_7_11_3_1_1540 7 37 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 133
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 37 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 133 (accept_3_3 5 37 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  133 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 37 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 133 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 37 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 133 (accept_3_3 2 37 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 133 (Polychromatic418967fa.accept_13_1_11_3_1_901 1 37 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 133))))))))))))))))))))))))))))))))))))) (allB_succ 36 133
  (allA_succ_of_accept 35 36 133 (accept_3_3 35 36 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  36 133 (Polychromatic418967fa.accept_14_6_8_7_1_589 34 36 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 36 133 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 36 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 36 133 (accept_3_3 32 36 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 133 (Polychromatic418967fa.accept_16_15_4_5_1_1411 31 36 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 36 133
  (Polychromatic418967fa.accept_21_9_15_7_1_5156 30 36 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 36 133 (accept_3_3 29 36 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  36 133 (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 36 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 36 133 (Polychromatic418967fa.accept_10_7_6_3_1_927 27 36 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 36 133 (accept_3_3 26 36 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 133 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 36 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 36 133
  (Polychromatic418967fa.accept_11_2_3_1_1_244 24 36 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 36 133 (accept_3_3 23 36 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  36 133 (Polychromatic418967fa.accept_15_7_6_13_1_936 22 36 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 36 133 (Polychromatic418967fa.accept_22_21_14_1_1_6716 21 36 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 36 133 (accept_3_3 20 36 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 133 (Polychromatic418967fa.accept_10_9_6_3_1_545 19 36 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 133
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 36 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 36 133 (accept_3_3 17 36 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  36 133 (Polychromatic418967fa.accept_17_16_2_14_1_6715 16 36 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 36 133 (Polychromatic418967fa.accept_13_2_10_3_1_1538 15 36 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 36 133 (accept_3_3 14 36 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 133 (Polychromatic418967fa.accept_11_2_3_1_1_244 13 36 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 36 133
  (Polychromatic418967fa.accept_16_12_4_5_1_2273 12 36 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 36 133 (accept_3_3 11 36 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  36 133 (Polychromatic418967fa.accept_21_10_15_7_1_3784 10 36 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 36 133 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 36 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 36 133 (accept_3_3 8 36 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 133 (Polychromatic418967fa.accept_10_7_6_3_1_927 7 36 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 36 133
  (Polychromatic418967fa.accept_13_6_10_3_1_897 6 36 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 36 133 (accept_3_3 5 36 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 36
  133 (Polychromatic418967fa.accept_15_4_6_13_1_956 4 36 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 36 133 (Polychromatic418967fa.accept_17_3_2_14_1_6714 3 36 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 36 133 (accept_3_3 2 36 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 133 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 36 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 133)))))))))))))))))))))))))))))))))))) (allB_succ 35
  133 (allA_of_3_1 35 35 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 34 133 (allA_succ_of_accept 33 34 133
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 34 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 34 133 (accept_3_3 32 34 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  34 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 34 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 34 133 (Polychromatic418967fa.accept_21_9_13_7_1_5154 30 34 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 133 (accept_3_3 29 34 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 34 133 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 34 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 34 133
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 34 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 34 133 (accept_3_3 26 34 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  34 133 (Polychromatic418967fa.accept_15_10_4_13_1_4506 25 34 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 34 133 (Polychromatic418967fa.accept_13_11_8_3_1_3016 24 34 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 133 (accept_3_3 23 34 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 34 133 (Polychromatic418967fa.accept_13_9_8_3_1_3045 22 34 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 34 133
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 34 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 34 133 (accept_3_3 20 34 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  34 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 34 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 34 133 (Polychromatic418967fa.accept_13_5_8_3_1_1535 18 34 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 34 133 (accept_3_3 17 34 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 34 133 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 34 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 34 133
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 34 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 34 133 (accept_3_3 14 34 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  34 133 (Polychromatic418967fa.accept_14_13_6_7_1_2013 13 34 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 34 133 (Polychromatic418967fa.accept_28_12_6_21_1_6713 12 34 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 133 (accept_3_3 11 34 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 34 133 (Polychromatic418967fa.accept_15_10_4_13_1_4506 10 34
  133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 34 133
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 34 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 34 133 (accept_3_3 8 34 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 34
  133 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 34 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 34 133 (Polychromatic418967fa.accept_15_6_4_13_1_403 6 34 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 133 (accept_3_3 5 34 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 34 133 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 34 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 34
  133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 34 133 (accept_3_3 2 34 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34 133 (Polychromatic418967fa.accept_14_1_6_7_1_1936 1
  34 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 133))))))))))))))))))))))))))))))))))
  (allB_succ 33 133 (allA_succ_of_accept 32 33 133 (accept_3_3 32 33 133 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 133 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 33 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 133 (Polychromatic418967fa.accept_9_3_6_7_1_562 30 33 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 133 (accept_3_3 29 33 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 28
  33 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 133
  (Polychromatic418967fa.accept_12_3_9_1_1_290 27 33 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 33 133 (accept_3_3 26 33 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  33 133 (Polychromatic418967fa.accept_15_10_3_13_1_4480 25 33 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 33 133 (Polychromatic418967fa.accept_13_11_7_3_1_894 24 33 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 133 (accept_3_3 23 33 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 33 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 133
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 33 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 33 133 (accept_3_3 20 33 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  33 133 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 33 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 33 133 (Polychromatic418967fa.accept_21_18_12_7_1_6712 18 33 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 133 (accept_3_3 17 33 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 33 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 133
  (Polychromatic418967fa.accept_12_3_9_1_1_290 15 33 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 33 133 (accept_3_3 14 33 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  33 133 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 33 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 33 133 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 33 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 133 (accept_3_3 11 33 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 33 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 133
  (Polychromatic418967fa.accept_13_9_7_3_1_1531 9 33 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 33 133 (accept_3_3 8 33 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33
  133 (Polychromatic418967fa.accept_22_7_11_1_1_6711 7 33 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 33 133 (Polychromatic418967fa.accept_16_6_1_5_1_2242 6 33 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 133 (accept_3_3 5 33 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 33 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33 133
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 33 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 33 133 (accept_3_3 2 33 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33
  133 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 33 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 33 133))))))))))))))))))))))))))))))))) (allB_succ 32 133 (allA_of_3_1 32 32 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 31 133 (allA_succ_of_accept 30 31 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 31
  133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 133 (accept_3_3 29 31 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 31 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 28
  31 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 133
  (Polychromatic418967fa.accept_13_1_5_3_1_888 27 31 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 31 133 (accept_3_3 26 31 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  31 133 (Polychromatic418967fa.accept_14_11_3_7_1_604 25 31 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 31 133 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 31 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 133 (accept_3_3 23 31 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 31 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 31 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 133
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 31 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 31 133 (accept_3_3 20 31 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  31 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 31 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 31 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 31 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 31 133 (accept_3_3 17 31 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 31 133 (Polychromatic418967fa.accept_21_16_10_7_1_3782 16 31 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 133
  (Polychromatic418967fa.accept_9_6_4_7_1_300 15 31 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 31 133 (accept_3_3 14 31 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  31 133 (Polychromatic418967fa.accept_21_13_10_7_1_3701 13 31 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 31 133 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 31 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 31 133 (accept_3_3 11 31 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 31 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 31 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 31 133
  (Polychromatic418967fa.accept_13_9_5_3_1_428 9 31 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 31 133 (accept_3_3 8 31 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 31
  133 (Polychromatic418967fa.accept_27_7_4_25_1_6710 7 31 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 31 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 31 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 31 133 (accept_3_3 5 31 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 31 133 (Polychromatic418967fa.accept_14_4_3_7_1_3702 4 31 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 31 133
  (Polychromatic418967fa.accept_9_3_4_7_1_89 3 31 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 31 133 (accept_3_3 2 31 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 31
  133 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 31 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 31 133))))))))))))))))))))))))))))))) (allB_succ 30 133 (allA_succ_of_accept 29 30 133 (accept_3_3 29 30 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 30 133 (Polychromatic418967fa.accept_9_1_3_7_1_6 28
  30 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 30 133
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 30 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 30 133 (accept_3_3 26 30 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  30 133 (Polychromatic418967fa.accept_13_12_4_3_1_1528 25 30 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 30 133 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 30 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 30 133 (accept_3_3 23 30 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 30 133 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 30 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 30 133
  (Polychromatic418967fa.accept_17_4_13_14_1_1139 21 30 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 30 133 (accept_3_3 20 30 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  30 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 30 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 30 133 (Polychromatic418967fa.accept_17_1_13_14_1_478 18 30 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 30 133 (accept_3_3 17 30 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 30 133 (Polychromatic418967fa.accept_21_16_9_7_1_6709 16 30
  133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 30 133
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 30 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 30 133 (accept_3_3 14 30 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  30 133 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 30 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 30 133 (Polychromatic418967fa.accept_13_12_4_3_1_1528 12 30 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 30 133 (accept_3_3 11 30 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 30 133 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 30 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 30 133
  (Polychromatic418967fa.accept_14_9_2_7_1_1242 9 30 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 30 133 (accept_3_3 8 30 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30
  133 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 30 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 30 133 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 30 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 30 133 (accept_3_3 5 30 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 30 133 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 30 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 30 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 30
  133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 30 133 (accept_3_3 2 30 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 133 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 30
  133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 133))))))))))))))))))))))))))))))
  (allB_succ 29 133 (allA_of_3_1 29 29 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 28 133
  (allA_succ_of_accept 27 28 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 28 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 28 133 (accept_3_3 26 28 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 28 133 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 28 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 28 133 (Polychromatic418967fa.accept_9_6_1_7_1_577 24
  28 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 133 (accept_3_3 23 28
  133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 28 133
  (Polychromatic418967fa.accept_9_4_1_7_1_293 22 28 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 28 133 7 3 4 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 28 133 (accept_3_3 20 28 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  28 133 (Polychromatic418967fa.accept_27_19_1_25_1_6708 19 28 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 28 133 (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 28 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 28 133 (accept_3_3 17 28 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 28 133 (Polychromatic418967fa.accept_10_6_8_3_1_930 16 28 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 28 133
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 28 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 28 133 7 2 4 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 28 133 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 28 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 28 133 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 28 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 28 133 (accept_3_3 11 28 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 28 133 (Polychromatic418967fa.accept_12_10_4_1_1_1843
  10 28 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 28 133
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 28 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 28 133 (accept_3_3 8 28 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 28 133
  7 1 4 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 28 133
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 28 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 28 133 (accept_3_3 5 28 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 28
  133 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 28 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 28 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 28 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 28 133 (accept_3_3 2 28 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 28 133 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 28 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 133)))))))))))))))))))))))))))) (allB_succ 27 133
  (allA_succ_of_accept 26 27 133 (accept_3_3 26 27 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  27 133 (Polychromatic418967fa.accept_10_5_7_3_1_561 25 27 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 27 133 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 27 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 133 (accept_3_3 23 27 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 27 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 133
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 27 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 27 133 (accept_3_3 20 27 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  27 133 (Polychromatic418967fa.accept_13_6_1_3_1_1522 19 27 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 27 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 27 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 133 (accept_3_3 17 27 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 27 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 133
  (Polychromatic418967fa.accept_10_5_7_3_1_561 15 27 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 27 133 (accept_3_3 14 27 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  27 133 (Polychromatic418967fa.accept_17_13_10_14_1_4211 13 27 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 27 133 (Polychromatic418967fa.accept_21_12_6_7_1_3739 12 27 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 133 (accept_3_3 11 27 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 27 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 133
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 27 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 27 133 (accept_3_3 8 27 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27
  133 (Polychromatic418967fa.accept_13_7_1_3_1_1523 7 27 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 27 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 27 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 133 (accept_3_3 5 27 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 27 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 133
  (Polychromatic418967fa.accept_15_3_12_13_1_2549 3 27 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 27 133 (accept_3_3 2 27 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27
  133 (Polychromatic418967fa.accept_14_1_13_7_1_1205 1 27 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 27 133))))))))))))))))))))))))))) (allB_succ 26 133 (allA_of_3_1 26 26 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 25 133 (allA_succ_of_accept 24 25 133 (Polychromatic418967fa.accept_11_2_3_1_1_244 24
  25 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 133 (accept_3_3 23 25
  133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 25 133
  (Polychromatic418967fa.accept_10_2_5_3_1_1408 22 25 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 25 133 (Polychromatic418967fa.accept_24_21_1_13_1_6707 21 25 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 133 (accept_3_3 20 25 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 25 133 (Polychromatic418967fa.accept_15_4_10_13_1_2565 19 25 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 133
  (Polychromatic418967fa.accept_10_8_5_3_1_543 18 25 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 133 (accept_3_3 17 25 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 133 (Polychromatic418967fa.accept_15_1_10_13_1_939 16 25 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 25 133 (Polychromatic418967fa.accept_13_2_12_3_1_415 15 25 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 133 (accept_3_3 14 25 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 133 (Polychromatic418967fa.accept_11_2_3_1_1_244 13 25 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 133
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 25 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 133 (accept_3_3 11 25 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  25 133 (Polychromatic418967fa.accept_14_10_11_7_1_1955 10 25 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 25 133 (Polychromatic418967fa.accept_13_9_12_3_1_907 9 25 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 133 (accept_3_3 8 25 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 133 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 25 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 133
  (Polychromatic418967fa.accept_17_6_8_14_1_6706 6 25 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 133 (accept_3_3 5 25 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25
  133 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 25 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 25 133 (Polychromatic418967fa.accept_14_3_11_7_1_1260 3 25 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 133 (accept_3_3 2 25 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 25 133 (Polychromatic418967fa.accept_15_1_10_13_1_939 1 25 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 133))))))))))))))))))))))))) (allB_succ 24 133
  (allA_succ_of_accept 23 24 133 (accept_3_3 23 24 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  24 133 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 24 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 24 133 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 24 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 24 133 (accept_3_3 20 24 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 24 133 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 24 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 24 133
  (Polychromatic418967fa.accept_13_5_11_3_1_902 18 24 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 24 133 (accept_3_3 17 24 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  24 133 (Polychromatic418967fa.accept_21_16_3_7_1_6705 16 24 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 24 133 (Polychromatic418967fa.accept_13_2_11_3_1_873 15 24 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 24 133 (accept_3_3 14 24 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 133 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 24 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 24 133
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 24 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 24 133 (accept_3_3 11 24 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  24 133 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 24 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 24 133 (Polychromatic418967fa.accept_10_9_4_3_1_539 9 24 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 24 133 (accept_3_3 8 24 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 133 (Polychromatic418967fa.accept_10_7_4_3_1_560 7 24 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 24 133
  (Polychromatic418967fa.accept_17_6_7_14_1_6704 6 24 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 24 133 (accept_3_3 5 24 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24
  133 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 24 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 24 133 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 24 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 24 133 (accept_3_3 2 24 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 24 133 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 24 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 133)))))))))))))))))))))))) (allB_succ 23 133 (allA_of_3_1 23 23
  133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 22 133 (allA_succ_of_accept 21 22 133
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 22 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 22 133 (accept_3_3 20 22 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  22 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 22 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 22 133 (Polychromatic418967fa.accept_13_5_9_3_1_870 18 22 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 133 (accept_3_3 17 22 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 22 133 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 22 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 22 133
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 22 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 22 133 (accept_3_3 14 22 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  22 133 (Polychromatic418967fa.accept_14_13_8_7_1_1224 13 22 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 22 133 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 22 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 22 133 (accept_3_3 11 22 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 22 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 22 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 22 133
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 22 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 22 133 (accept_3_3 8 22 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 22
  133 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 22 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 22 133 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 22 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 133 (accept_3_3 5 22 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 22 133 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 22 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 22 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 22
  133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 22 133 (accept_3_3 2 22 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 22 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 22
  133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 133)))))))))))))))))))))) (allB_succ 21
  133 (allA_succ_of_accept 20 21 133 (accept_3_3 20 21 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 21 133 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 21 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 21 133 (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 21 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 133 (accept_3_3 17 21 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 21 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 133
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 21 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 21 133 7 2 3 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 21 133 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 21 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 133 (Polychromatic418967fa.accept_10_2_1_3_1_233 12 21 133
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 133 (accept_3_3 11 21 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 10
  21 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 133
  (Polychromatic418967fa.accept_11_9_10_1_1_581 9 21 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 21 133 (accept_3_3 8 21 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 21 133
  7 1 3 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 21 133
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 21 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 133 (accept_3_3 5 21 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21
  133 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 21 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 21 133 (Polychromatic418967fa.accept_12_3_9_1_1_290 3 21 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 133 (accept_3_3 2 21 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 21 133 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 21 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 133))))))))))))))))))))) (allB_succ 20 133 (allA_of_3_1 20 20
  133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 19 133 (allA_succ_of_accept 18 19 133
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 19 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 133 (accept_3_3 17 19 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 133 (Polychromatic418967fa.accept_10_6_9_3_1_935 16 19 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 133 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 19 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 133 (accept_3_3 14 19 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 133 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 19 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 133
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 19 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 133 (accept_3_3 11 19 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 19 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 133 (Polychromatic418967fa.accept_13_9_6_3_1_1514 9 19 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 133 (accept_3_3 8 19 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 133 (Polychromatic418967fa.accept_24_7_19_13_1_6703 7 19 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 133
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 19 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 133 (accept_3_3 5 19 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  133 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 19 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 133 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 19 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 133 (accept_3_3 2 19 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 133 (Polychromatic418967fa.accept_13_1_6_3_1_1547 1 19 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 133))))))))))))))))))) (allB_succ 18 133 (allA_succ_of_accept 17
  18 133 (accept_3_3 17 18 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 133
  (Polychromatic418967fa.accept_10_6_8_3_1_930 16 18 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 18 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 18 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 133 (accept_3_3 14 18 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 18 133 (Polychromatic418967fa.accept_16_13_2_5_1_3336 13 18 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 18 133
  (Polychromatic418967fa.accept_15_12_3_13_1_4481 12 18 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 18 133 (accept_3_3 11 18 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  18 133 (Polychromatic418967fa.accept_14_10_4_7_1_1214 10 18 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 18 133 (Polychromatic418967fa.accept_13_9_5_3_1_428 9 18 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 133 (accept_3_3 8 18 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 18 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 18 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18 133
  (Polychromatic418967fa.accept_10_6_8_3_1_930 6 18 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 18 133 (accept_3_3 5 18 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18
  133 (Polychromatic418967fa.accept_17_4_1_14_1_4296 4 18 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 18 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 18 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 18 133 (accept_3_3 2 18 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 133 (Polychromatic418967fa.accept_10_1_8_3_1_947 1 18 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 133)))))))))))))))))) (allB_succ 17 133 (allA_of_3_1
  17 17 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 16 133 (allA_succ_of_accept 15 16 133
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 16 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 16 133 (accept_3_3 14 16 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  16 133 (Polychromatic418967fa.accept_21_13_16_7_1_3712 13 16 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 16 133 (Polychromatic418967fa.accept_14_12_2_7_1_1243 12 16 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 16 133 (accept_3_3 11 16 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 16 133 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 16
  133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 16 133
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 16 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 16 133 (accept_3_3 8 16 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 16
  133 (Polychromatic418967fa.accept_10_7_6_3_1_927 7 16 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 16 133 (Polychromatic418967fa.accept_11_6_5_1_1_586 6 16 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 16 133 (accept_3_3 5 16 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 16 133 (Polychromatic418967fa.accept_18_4_16_7_1_1873 4 16 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 16 133 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 16
  133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 16 133 (accept_3_3 2 16 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 16 133 (Polychromatic418967fa.accept_18_1_16_7_1_2897
  1 16 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 133)))))))))))))))) (allB_succ 15
  133 (allA_succ_of_accept 14 15 133 (accept_3_3 14 15 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 15 133 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 15 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 15 133 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 15 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 133 (accept_3_3 11 15 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 15 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 133
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 15 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 15 133 (accept_3_3 8 15 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15
  133 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 15 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 15 133 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 15 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 15 133 (accept_3_3 5 15 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 15 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 15 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 15 133 (Polychromatic418967fa.accept_9_3_6_7_1_562 3
  15 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 133 (accept_3_3 2 15 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 133 (Polychromatic418967fa.accept_9_1_6_7_1_285 1
  15 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 133))))))))))))))) (allB_succ 14 133
  (allA_of_3_1 14 14 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 133 (allA_succ_of_accept 12 13 133
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 13 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 133 (accept_3_3 11 13 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 13 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 133 (Polychromatic418967fa.accept_16_9_13_5_1_2238 9 13 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 133 (accept_3_3 8 13 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 133 (Polychromatic418967fa.accept_23_7_13_18_1_6702 7 13 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 133
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 13 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 133 (accept_3_3 5 13 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  133 (Polychromatic418967fa.accept_17_4_13_14_1_1139 4 13 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 13 133 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 13 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 133 (accept_3_3 2 13 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 133 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 13 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 133))))))))))))) (allB_succ 12 133
  (allA_succ_of_accept 11 12 133 (accept_3_3 11 12 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  12 133 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 12 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 12 133 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 12 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 133 (accept_3_3 8 12 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 12 133 (Polychromatic418967fa.accept_16_7_12_5_1_734 7 12 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12 133
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 12 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 12 133 (accept_3_3 5 12 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12
  133 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 12 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 12 133 (Polychromatic418967fa.accept_15_3_12_13_1_2549 3 12 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 12 133 (accept_3_3 2 12 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 12 133 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 12 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 133)))))))))))) (allB_succ 11 133 (allA_of_3_1 11 11 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 10 133 (allA_succ_of_accept 9 10 133
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 10 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 10 133 (accept_3_3 8 10 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 10
  133 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 10 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 10 133 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 10 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 10 133 (accept_3_3 5 10 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 10 133 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 10 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 10 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 10
  133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 10 133 (accept_3_3 2 10 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 10 133 (Polychromatic418967fa.accept_15_1_10_13_1_939
  1 10 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 133)))))))))) (allB_succ 9 133
  (allA_succ_of_accept 8 9 133 (accept_3_3 8 9 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 133
  (Polychromatic418967fa.accept_13_7_9_3_1_1504 7 9 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 9 133 (Polychromatic418967fa.accept_10_6_9_3_1_935 6 9 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 133 (accept_3_3 5 9 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 9 133 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 9 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 133 (Polychromatic418967fa.accept_12_3_9_1_1_290 3 9
  133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 133 (accept_3_3 2 9 133
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 133 (Polychromatic418967fa.accept_16_1_9_5_1_5443 1
  9 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 133))))))))) (allB_succ 8 133
  (allA_of_3_1 8 8 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 7 133 (allA_succ_of_accept 6 7 133
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 7 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 133 (accept_3_3 5 7 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 133
  (Polychromatic418967fa.accept_10_4_7_3_1_54 4 7 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 133 (Polychromatic418967fa.accept_25_3_7_8_1_6701 3 7 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 133 (accept_3_3 2 7 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 133 (Polychromatic418967fa.accept_13_1_7_3_1_1503 1 7 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 133))))))) (allB_succ 6 133 (allA_succ_of_accept 5 6 133
  (accept_3_3 5 6 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 6 133
  (Polychromatic418967fa.accept_9_4_6_7_1_286 4 6 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 6 133 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 6 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 6 133 (accept_3_3 2 6 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 6 133 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 6 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 133)))))) (allB_succ 5 133 (allA_of_3_1 5 5 133 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 4 133 (allA_succ_of_accept 3 4 133
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 4 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 133 (accept_3_3 2 4 133 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 133
  (Polychromatic418967fa.accept_8_1_4_5_1_48 1 4 133 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 133)))) (allB_succ 3 133 (allA_succ_of_accept 2 3 133 (accept_3_3 2 3 133 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 133 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 3 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 133))) (allB_succ 2 133 (allA_of_3_1 2 2 133 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  133)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


