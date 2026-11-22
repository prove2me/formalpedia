-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch137
-- name    : Polychromatic418967fa_Branch137
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:13:38.939856+00:00
-- url     : https://prove2.me/theorems/dcca5f04-f531-4abc-aaae-0691a76f3621
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

def Polychromatic418967fa.branch_137 : allB 137 137 :=
  allB_succ' 2 136 137 (Eq.refl Bool.true) (allA_of_3_0 2 136 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  135 137 (Eq.refl Bool.true) (allA_succ_of_accept 2 135 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 135 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 137 (accept_3_2 1 135 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135 137))) (allB_succ' 4 134 137 (Eq.refl Bool.true)
  (allA_succ_of_accept 3 134 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 134 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 134 137 (Polychromatic418967fa.accept_10_2_4_7_1_352 2 134 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 134 137 (accept_3_2 1 134 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134 137)))) (allB_succ' 5 133 137 (Eq.refl Bool.true) (allA_of_3_0
  5 133 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 6 132 137 (Eq.refl Bool.true) (allA_succ_of_accept 5
  132 137 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 132 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 132 137 (accept_3_2 4 132 137 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 132 137 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 132 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 132 137 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 132 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 132 137 (accept_3_2 1 132 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132 137)))))) (allB_succ' 7 131 137 (Eq.refl Bool.true)
  (allA_succ_of_accept 6 131 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 131 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 131 137 (Polychromatic418967fa.accept_15_5_11_2_1_1095 5 131
  137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 131 137 (accept_3_2 4 131 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 131 137 (Polychromatic418967fa.accept_9_3_5_2_1_28 3
  131 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 131 137
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 131 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 131 137 (accept_3_2 1 131 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 131 137)))))))
  (allB_succ' 8 130 137 (Eq.refl Bool.true) (allA_of_3_0 8 130 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  9 129 137 (Eq.refl Bool.true) (allA_succ_of_accept 8 129 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 129 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 137 (accept_3_2 7 129 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 129 137 (Polychromatic418967fa.accept_7_6_3_4_1_294 6
  129 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 129 137
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 129 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 129 137 (accept_3_2 4 129 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  129 137 (Polychromatic418967fa.accept_11_3_8_5_1_336 3 129 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 129 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 129 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 137 (accept_3_2 1 129 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 129 137))))))))) (allB_succ' 10 128 137 (Eq.refl Bool.true) (allA_succ_of_accept 9 128
  137 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 128 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 128 137 (Polychromatic418967fa.accept_17_8_9_1_1_3340 8 128 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 128 137 (accept_3_2 7 128 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 128 137 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 128 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 128 137 (Polychromatic418967fa.accept_7_5_2_4_1_126 5
  128 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 128 137 (accept_3_2 4 128
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 128 137 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 128 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 128 137
  (Polychromatic418967fa.accept_12_2_8_5_1_408 2 128 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 128 137 (accept_3_2 1 128 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128
  137)))))))))) (allB_succ' 11 127 137 (Eq.refl Bool.true) (allA_of_3_0 11 127 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 126 137 (Eq.refl Bool.true) (allA_succ_of_accept 11 126 137
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 126 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 126 137 (accept_3_2 10 126 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  126 137 (Polychromatic418967fa.accept_20_9_6_17_1_1654 9 126 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 126 137 (Polychromatic418967fa.accept_13_8_9_7_1_530 8 126 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 126 137 (accept_3_2 7 126 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 126 137 (Polychromatic418967fa.accept_13_6_9_7_1_2430 6 126 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 126 137
  (Polychromatic418967fa.accept_16_5_14_9_1_2572 5 126 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 126 137 (accept_3_2 4 126 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  126 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 126 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 126 137 (Polychromatic418967fa.accept_13_2_9_7_1_164 2 126 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 126 137 (accept_3_2 1 126 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 126 137)))))))))))) (allB_succ' 13 125 137 (Eq.refl Bool.true) (allA_succ_of_accept 12
  125 137 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 125 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 125 137 (Polychromatic418967fa.accept_15_11_5_2_1_520 11 125 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 125 137 (accept_3_2 10 125 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 125 137 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 125 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 125 137
  (Polychromatic418967fa.accept_10_8_5_7_1_358 8 125 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 125 137 (accept_3_2 7 125 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  125 137 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 125 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 125 137 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 125 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 125 137 (accept_3_2 4 125 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 125 137 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 125 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 125 137
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 125 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 125 137 (accept_3_2 1 125 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 125
  137))))))))))))) (allB_succ' 14 124 137 (Eq.refl Bool.true) (allA_of_3_0 14 124 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 123 137 (Eq.refl Bool.true) (allA_succ_of_accept 14 123 137
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 123 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 123 137 (accept_3_2 13 123 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 123 137 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 123 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 123 137 (Polychromatic418967fa.accept_22_11_13_5_1_7084 11 123 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 123 137 (accept_3_2 10 123 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 123 137 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 123 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 123 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 123 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 123 137 (accept_3_2 7 123 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  123 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 123 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 123 137 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 123 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 137 (accept_3_2 4 123 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 123 137 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 123 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 123 137
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 123 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 123 137 (accept_3_2 1 123 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 123
  137))))))))))))))) (allB_succ' 16 122 137 (Eq.refl Bool.true) (allA_succ_of_accept 15 122 137
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 122 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 122 137 (Polychromatic418967fa.accept_10_4_2_7_1_373 14 122 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 122 137 (accept_3_2 13 122 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 122 137 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 122 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 122 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 11
  122 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 122 137 (accept_3_2 10
  122 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 122 137
  (Polychromatic418967fa.accept_6_3_2_5_1_32 9 122 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 122 137 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 122 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 122 137 (accept_3_2 7 122 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 122 137 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 122 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 122 137 (Polychromatic418967fa.accept_10_5_2_7_1_345 5
  122 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 122 137 (accept_3_2 4 122
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 122 137 (Polychromatic418967fa.accept_4_3_2_1_1_50
  3 122 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 122 137
  (Polychromatic418967fa.accept_13_2_5_7_1_1695 2 122 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 122 137 (accept_3_2 1 122 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  137)))))))))))))))) (allB_succ' 17 121 137 (Eq.refl Bool.true) (allA_of_3_0 17 121 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 18 120 137 (Eq.refl Bool.true) (allA_succ_of_accept 17 120 137
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 120 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 120 137 (accept_3_2 16 120 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 120 137 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 120 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 120 137 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 120 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 120 137 (accept_3_2 13 120 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 120 137 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 120 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 120 137
  (Polychromatic418967fa.accept_13_11_3_7_1_2513 11 120 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 120 137 (accept_3_2 10 120 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  120 137 (Polychromatic418967fa.accept_13_9_3_7_1_1065 9 120 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 120 137 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 120 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 120 137 (accept_3_2 7 120 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 120 137 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 120 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 120 137
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 120 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 120 137 (accept_3_2 4 120 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  120 137 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 120 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 120 137 (Polychromatic418967fa.accept_19_2_6_4_1_4251 2 120 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 120 137 (accept_3_2 1 120 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 120 137)))))))))))))))))) (allB_succ' 19 119 137 (Eq.refl Bool.true)
  (allA_succ_of_accept 18 119 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 119 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 119 137 (Polychromatic418967fa.accept_14_3_7_11_1_765 17 119
  137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 119 137 (accept_3_2 16 119
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 119 137
  (Polychromatic418967fa.accept_19_15_5_4_1_1867 15 119 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 119 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 119 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 119 137 (accept_3_2 13 119 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 119 137 (Polychromatic418967fa.accept_10_2_9_7_1_720 12 119 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 119 137
  (Polychromatic418967fa.accept_22_11_9_5_1_7083 11 119 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 119 137 (accept_3_2 10 119 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  119 137 (Polychromatic418967fa.accept_13_9_2_7_1_1083 9 119 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 119 137 (Polychromatic418967fa.accept_10_8_9_7_1_1118 8 119 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 119 137 (accept_3_2 7 119 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 119 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 119 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 119 137
  (Polychromatic418967fa.accept_13_5_2_7_1_2414 5 119 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 119 137 (accept_3_2 4 119 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  119 137 (Polychromatic418967fa.accept_14_3_7_11_1_765 3 119 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 119 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 119 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 119 137 (accept_3_2 1 119 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 119 137))))))))))))))))))) (allB_succ' 20 118 137 (Eq.refl Bool.true) (allA_of_3_0 20
  118 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 21 117 137 (Eq.refl Bool.true) (allA_succ_of_accept 20
  117 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 117 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 117 137 (accept_3_2 19 117 137 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 117 137 (Polychromatic418967fa.accept_15_3_12_2_1_507 18 117 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 117 137 (Polychromatic418967fa.accept_16_1_5_9_1_1649 17 117
  137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 137 (accept_3_2 16 117
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 117 137
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 117 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 117 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 117 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 137 (accept_3_2 13 117 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 117 137 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 117 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 117 137
  (Polychromatic418967fa.accept_16_11_5_9_1_1617 11 117 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 117 137 (accept_3_2 10 117 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  117 137 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 117 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 117 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 117 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 137 (accept_3_2 7 117 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 137 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 117 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 117 137
  (Polychromatic418967fa.accept_15_5_12_2_1_2820 5 117 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 117 137 (accept_3_2 4 117 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  117 137 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 117 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 117 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 117 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 137 (accept_3_2 1 117 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 117 137))))))))))))))))))))) (allB_succ' 22 116 137 (Eq.refl Bool.true)
  (allA_succ_of_accept 21 116 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 116 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 116 137 (Polychromatic418967fa.accept_15_5_11_2_1_1095 20 116
  137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 116 137 (accept_3_2 19 116
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 116 137
  (Polychromatic418967fa.accept_13_5_12_7_1_1080 18 116 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 116 137 (Polychromatic418967fa.accept_13_4_12_7_1_2439 17 116 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 116 137 (accept_3_2 16 116 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 116 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 116 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 116 137 (Polychromatic418967fa.accept_9_5_8_2_1_409
  14 116 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 116 137 (accept_3_2 13
  116 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 116 137
  (Polychromatic418967fa.accept_9_3_8_2_1_162 12 116 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 116 137 (Polychromatic418967fa.accept_10_1_6_7_1_710 11 116 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 116 137 (accept_3_2 10 116 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 116 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 116 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 116 137 (Polychromatic418967fa.accept_13_8_12_7_1_2442
  8 116 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 116 137 (accept_3_2 7
  116 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 116 137
  (Polychromatic418967fa.accept_9_6_8_2_1_410 6 116 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 116 137 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 116 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 116 137 (accept_3_2 4 116 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 116 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 116 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 116 137 (Polychromatic418967fa.accept_12_2_8_5_1_408 2
  116 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 116 137 (accept_3_2 1 116
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116 137)))))))))))))))))))))) (allB_succ' 23 115 137 (Eq.refl
  Bool.true) (allA_of_3_0 23 115 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 114 137 (Eq.refl Bool.true)
  (allA_succ_of_accept 23 114 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 114 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 114 137 (accept_3_2 22 114 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 114 137 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 114 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 114 137 (Polychromatic418967fa.accept_7_6_2_4_1_291
  20 114 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 114 137 (accept_3_2 19
  114 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 114 137
  (Polychromatic418967fa.accept_21_18_9_11_1_7082 18 114 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 114 137 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 114 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 114 137 (accept_3_2 16 114 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 114 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 114 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 114 137
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 114 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 114 137 (accept_3_2 13 114 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 114 137 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 114 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 114 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 114 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 114 137 (accept_3_2 10 114 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 114 137 (Polychromatic418967fa.accept_14_9_2_11_1_780 9 114 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 114 137
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 114 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 114 137 (accept_3_2 7 114 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  114 137 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 114 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 114 137 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 114 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 114 137 (accept_3_2 4 114 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 114 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 114 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 114 137
  (Polychromatic418967fa.accept_10_2_4_7_1_352 2 114 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 114 137 (accept_3_2 1 114 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  137)))))))))))))))))))))))) (allB_succ' 25 113 137 (Eq.refl Bool.true) (allA_succ_of_accept 24 113 137
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 113 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 113 137 (Polychromatic418967fa.accept_22_1_3_5_1_375 23 113 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 113 137 (accept_3_2 22 113 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 113 137 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 113 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 137
  (Polychromatic418967fa.accept_21_20_8_11_1_5407 20 113 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 113 137 (accept_3_2 19 113 137 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 113 137 (Polychromatic418967fa.accept_14_4_1_11_1_5026 18 113 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 113 137 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 113 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 137 (accept_3_2 16 113 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 113 137 (Polychromatic418967fa.accept_9_6_5_2_1_421
  15 113 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 137
  (Polychromatic418967fa.accept_10_4_3_7_1_1110 14 113 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 113 137 (accept_3_2 13 113 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 113 137 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 113 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 113 137 (Polychromatic418967fa.accept_13_11_9_7_1_2484 11 113 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 137 (accept_3_2 10 113 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 137 (Polychromatic418967fa.accept_15_9_8_2_1_1109 9 113 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 137
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 113 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 113 137 (accept_3_2 7 113 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  113 137 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 113 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 113 137 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 113 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 137 (accept_3_2 4 113 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 137 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 113 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 137
  (Polychromatic418967fa.accept_13_2_9_7_1_164 2 113 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 137 (accept_3_2 1 113 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  137))))))))))))))))))))))))) (allB_succ' 26 112 137 (Eq.refl Bool.true) (allA_of_3_0 26 112 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 27 111 137 (Eq.refl Bool.true) (allA_succ_of_accept 26 111 137
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 111 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 111 137 (accept_3_2 25 111 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 111 137 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 111 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 111 137 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 111 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 111 137 (accept_3_2 22 111 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 111 137 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 111 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 111 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 111 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 111 137 (accept_3_2 19 111 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 111 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 111 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 111 137 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 111 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 137 (accept_3_2 16 111 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 111 137 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 111 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 111 137
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 111 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 111 137 (accept_3_2 13 111 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 111 137 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 111 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 111 137 (Polychromatic418967fa.accept_15_11_6_2_1_1106 11 111 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 137 (accept_3_2 10 111 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 111 137 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 111 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 111 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 111 137 (accept_3_2 7 111 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  111 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 111 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 111 137 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 111 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 137 (accept_3_2 4 111 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 111 137 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 111 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 137
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 111 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 111 137 (accept_3_2 1 111 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111
  137))))))))))))))))))))))))))) (allB_succ' 28 110 137 (Eq.refl Bool.true) (allA_succ_of_accept 27 110 137
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 110 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 110 137 (Polychromatic418967fa.accept_15_11_5_2_1_520 26 110 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 110 137 (accept_3_2 25 110 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 110 137 (Polychromatic418967fa.accept_17_7_8_1_1_1373 24 110 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 110 137
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 110 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 110 137 (accept_3_2 22 110 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 110 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 110 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 110 137 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 110 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 110 137 (accept_3_2 19 110 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 110 137 (Polychromatic418967fa.accept_15_3_5_2_1_2816 18 110 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 110 137
  (Polychromatic418967fa.accept_13_4_6_7_1_2471 17 110 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 110 137 (accept_3_2 16 110 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 110 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 110 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 110 137 (Polychromatic418967fa.accept_13_1_6_7_1_550 14 110 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 110 137 (accept_3_2 13 110 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 110 137 (Polychromatic418967fa.accept_13_12_6_7_1_1071 12 110
  137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 110 137
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 110 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 110 137 (accept_3_2 10 110 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  110 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 110 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 110 137 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 110 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 110 137 (accept_3_2 7 110 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 110 137 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 110 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 110 137
  (Polychromatic418967fa.accept_16_5_14_9_1_2572 5 110 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 110 137 (accept_3_2 4 110 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  110 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 110 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 110 137 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 110 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 110 137 (accept_3_2 1 110 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 110 137)))))))))))))))))))))))))))) (allB_succ' 29 109 137 (Eq.refl Bool.true)
  (allA_of_3_0 29 109 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 30 108 137 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 108 137 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 108 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 108 137 (accept_3_2 28 108 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 108 137 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 108 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 108 137
  (Polychromatic418967fa.accept_19_7_13_4_1_1824 26 108 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 108 137 (accept_3_2 25 108 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 108 137 (Polychromatic418967fa.accept_13_11_4_7_1_2419 24 108 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 108 137 (Polychromatic418967fa.accept_13_10_4_7_1_2465 23 108 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 108 137 (accept_3_2 22 108 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 108 137 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 108 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 108 137
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 108 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 108 137 (accept_3_2 19 108 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 108 137 (Polychromatic418967fa.accept_11_7_9_5_1_338 18 108 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 108 137 (Polychromatic418967fa.accept_19_17_13_4_1_7081 17 108 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 108 137 (accept_3_2 16 108 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 108 137 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 108 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 108 137
  (Polychromatic418967fa.accept_15_14_3_2_1_2811 14 108 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 108 137 (accept_3_2 13 108 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 108 137 (Polychromatic418967fa.accept_13_12_4_7_1_2520 12 108 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 108 137 (Polychromatic418967fa.accept_13_11_4_7_1_2419 11 108 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 108 137 (accept_3_2 10 108 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 108 137 (Polychromatic418967fa.accept_10_9_8_7_1_714 9 108 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 108 137
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 108 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 108 137 (accept_3_2 7 108 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  108 137 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 108 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 108 137 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 108 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 108 137 (accept_3_2 4 108 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 108 137 (Polychromatic418967fa.accept_13_3_4_7_1_1711 3 108 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 108 137
  (Polychromatic418967fa.accept_16_2_12_9_1_2568 2 108 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 108 137 (accept_3_2 1 108 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  137)))))))))))))))))))))))))))))) (allB_succ' 31 107 137 (Eq.refl Bool.true) (allA_succ_of_accept 30 107 137
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 107 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 107 137 (Polychromatic418967fa.accept_20_9_7_17_1_1655 29 107 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 107 137 (accept_3_2 28 107 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 107 137 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 107 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 107 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 26
  107 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 107 137 (accept_3_2 25
  107 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 107 137
  (Polychromatic418967fa.accept_9_6_8_2_1_410 24 107 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 107 137 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 107 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 107 137 (accept_3_2 22 107 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 107 137 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 107 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 107 137 (Polychromatic418967fa.accept_7_6_2_4_1_291
  20 107 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 107 137 (accept_3_2 19
  107 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 107 137
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 107 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 107 137 (Polychromatic418967fa.accept_13_4_3_7_1_2515 17 107 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 107 137 (accept_3_2 16 107 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 107 137 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 107 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 14
  107 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 107 137 (accept_3_2 13
  107 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 107 137
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 107 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 107 137 (Polychromatic418967fa.accept_13_11_3_7_1_2513 11 107 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 137 (accept_3_2 10 107 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 107 137 (Polychromatic418967fa.accept_13_9_3_7_1_1065 9 107 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 137 (Polychromatic418967fa.accept_13_8_3_7_1_2455
  8 107 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 107 137 (accept_3_2 7
  107 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 107 137
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 107 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 107 137 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 107 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 137 (accept_3_2 4 107 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 107 137 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 107 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 2
  107 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 107 137 (accept_3_2 1 107
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107 137))))))))))))))))))))))))))))))) (allB_succ' 32 106 137
  (Eq.refl Bool.true) (allA_of_3_0 32 106 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 105 137 (Eq.refl
  Bool.true) (allA_succ_of_accept 32 105 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 105 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 137 (accept_3_2 31 105 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 105 137 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 105 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 105 137
  (Polychromatic418967fa.accept_13_3_1_7_1_1706 29 105 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 105 137 (accept_3_2 28 105 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 105 137 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 105 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 105 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 105 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 137 (accept_3_2 25 105 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 105 137 (Polychromatic418967fa.accept_13_11_1_7_1_1691 24 105 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 105 137
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 105 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 105 137 (accept_3_2 22 105 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 105 137 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 105 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 105 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 105 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 137 (accept_3_2 19 105 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 137 (Polychromatic418967fa.accept_10_8_5_7_1_358 18 105 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 137
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 105 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 105 137 (accept_3_2 16 105 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 105 137 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 105 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 105 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 105 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 137 (accept_3_2 13 105 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 137 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 105 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 137
  (Polychromatic418967fa.accept_13_11_1_7_1_1691 11 105 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 105 137 (accept_3_2 10 105 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  105 137 (Polychromatic418967fa.accept_17_9_3_1_1_2275 9 105 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 105 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 105 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 137 (accept_3_2 7 105 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 105 137 (Polychromatic418967fa.accept_13_6_1_7_1_1690 6 105 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 105 137
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 105 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 105 137 (accept_3_2 4 105 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  105 137 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 105 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 105 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 105 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 137 (accept_3_2 1 105 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 105 137))))))))))))))))))))))))))))))))) (allB_succ' 34 104 137 (Eq.refl Bool.true)
  (allA_succ_of_accept 33 104 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 104 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 104 137 (Polychromatic418967fa.accept_10_2_4_7_1_352 32 104
  137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 104 137 (accept_3_2 31 104
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 104 137
  (Polychromatic418967fa.accept_7_2_6_4_1_29 30 104 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 104 137 (Polychromatic418967fa.accept_19_10_9_4_1_5620 29 104 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 104 137 (accept_3_2 28 104 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 104 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 104 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 104 137 (Polychromatic418967fa.accept_7_5_6_4_1_117
  26 104 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 104 137 (accept_3_2 25
  104 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 104 137
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 104 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 104 137 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 104 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 104 137 (accept_3_2 22 104 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 104 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 104 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 104 137
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 20 104 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 104 137 (accept_3_2 19 104 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 104 137 (Polychromatic418967fa.accept_15_3_14_2_1_1888 18 104 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 104 137 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 104 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 104 137 (accept_3_2 16 104 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 104 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 104 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 104 137
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 104 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 104 137 (accept_3_2 13 104 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 104 137 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 104 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 104 137 (Polychromatic418967fa.accept_10_1_4_7_1_374 11 104 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 104 137 (accept_3_2 10 104 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 104 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 104 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 104 137
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 104 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 104 137 (accept_3_2 7 104 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  104 137 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 104 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 104 137 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 104 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 104 137 (accept_3_2 4 104 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 104 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 104 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 104 137
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 104 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 104 137 (accept_3_2 1 104 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  137)))))))))))))))))))))))))))))))))) (allB_succ' 35 103 137 (Eq.refl Bool.true) (allA_of_3_0 35 103 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 102 137 (Eq.refl Bool.true) (allA_succ_of_accept 35 102 137
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 102 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 102 137 (accept_3_2 34 102 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 102 137 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 102 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 102 137 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 102 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 102 137 (accept_3_2 31 102 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 102 137 (Polychromatic418967fa.accept_11_8_3_5_1_355 30 102 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 102 137
  (Polychromatic418967fa.accept_10_9_2_7_1_1096 29 102 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 102 137 (accept_3_2 28 102 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 102 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 102 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 102 137 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 102 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 102 137 (accept_3_2 25 102 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 102 137 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 102 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 102 137
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 102 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 102 137 (accept_3_2 22 102 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 102 137 (Polychromatic418967fa.accept_14_7_4_11_1_3038 21 102 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 102 137 (Polychromatic418967fa.accept_15_5_12_2_1_2820 20 102 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 102 137 (accept_3_2 19 102 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 102 137 (Polychromatic418967fa.accept_13_5_11_7_1_559 18 102
  137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 102 137
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 102 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 102 137 (accept_3_2 16 102 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 102 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 102 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 102 137 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 102 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 102 137 (accept_3_2 13 102 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 102 137 (Polychromatic418967fa.accept_13_12_11_7_1_2491 12 102 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 102 137
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 102 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 102 137 (accept_3_2 10 102 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  102 137 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 102 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 102 137 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 102 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 102 137 (accept_3_2 7 102 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 102 137 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 102 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 102 137
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 102 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 102 137 (accept_3_2 4 102 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  102 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 102 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 102 137 (Polychromatic418967fa.accept_16_2_6_9_1_3473 2 102 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 102 137 (accept_3_2 1 102 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 102 137)))))))))))))))))))))))))))))))))))) (allB_succ' 37 101 137 (Eq.refl Bool.true)
  (allA_succ_of_accept 36 101 137 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 101 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 101 137 (Polychromatic418967fa.accept_14_7_3_11_1_2199 35 101
  137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 101 137 (accept_3_2 34 101
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 101 137
  (Polychromatic418967fa.accept_16_1_5_9_1_1649 33 101 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 101 137 (Polychromatic418967fa.accept_17_15_16_1_1_7080 32 101 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 101 137 (accept_3_2 31 101 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 101 137 (Polychromatic418967fa.accept_11_8_2_5_1_1769 30 101 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 101 137
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 101 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 101 137 (accept_3_2 28 101 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 101 137 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 101 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 101 137 (Polychromatic418967fa.accept_10_6_1_7_1_342 26 101 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 101 137 (accept_3_2 25 101 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 101 137 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 101
  137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 101 137
  (Polychromatic418967fa.accept_21_2_17_11_1_7037 23 101 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 101 137 (accept_3_2 22 101 137 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 101 137 (Polychromatic418967fa.accept_13_8_10_7_1_1702 21 101 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 101 137 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 101 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 101 137 (accept_3_2 19 101 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 101 137
  (Polychromatic418967fa.accept_20_18_1_17_1_4085 18 101 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 101 137 (Polychromatic418967fa.accept_13_4_10_7_1_1701 17 101 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 137 (accept_3_2 16 101 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 101 137 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 101 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 101 137
  (Polychromatic418967fa.accept_10_4_1_7_1_371 14 101 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 101 137 (accept_3_2 13 101 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 101 137 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 101 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 101 137 (Polychromatic418967fa.accept_16_11_5_9_1_1617 11 101 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 137 (accept_3_2 10 101 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 101 137 (Polychromatic418967fa.accept_15_9_11_2_1_1882 9 101
  137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 137
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 101 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 101 137 (accept_3_2 7 101 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  101 137 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 101 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 101 137 (Polychromatic418967fa.accept_15_5_11_2_1_1095 5 101 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 137 (accept_3_2 4 101 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 137 (Polychromatic418967fa.accept_13_3_10_7_1_1061 3 101
  137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 137
  (Polychromatic418967fa.accept_17_2_16_1_1_2260 2 101 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 101 137 (accept_3_2 1 101 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101
  137))))))))))))))))))))))))))))))))))))) (allB_succ' 38 100 137 (Eq.refl Bool.true) (allA_of_3_0 38 100 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 99 137 (Eq.refl Bool.true) (allA_succ_of_accept 38 99 137
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 99 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 99 137 (accept_3_2 37 99 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  99 137 (Polychromatic418967fa.accept_13_10_8_7_1_1074 36 99 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 99 137 (Polychromatic418967fa.accept_13_9_8_7_1_1073 35 99 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 137 (accept_3_2 34 99 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 137 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 99 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 99 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 99 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 99 137 (accept_3_2 31 99 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  99 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 99 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 99 137 (Polychromatic418967fa.accept_13_3_8_7_1_4135 29 99 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 137 (accept_3_2 28 99 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 137 (Polychromatic418967fa.accept_13_1_8_7_1_1088 27 99 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 99 137
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 99 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 99 137 (accept_3_2 25 99 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  99 137 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 99 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 99 137 (Polychromatic418967fa.accept_13_10_8_7_1_1074 23 99 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 137 (accept_3_2 22 99 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 137 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 99 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 99 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 99 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 137 (accept_3_2 19 99 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  99 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 99 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 99 137 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 99 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 137 (accept_3_2 16 99 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 137 (Polychromatic418967fa.accept_13_2_8_7_1_2424 15 99 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 99 137
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 99 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 99 137 (accept_3_2 13 99 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  99 137 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 99 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 99 137 (Polychromatic418967fa.accept_15_11_9_2_1_4780 11 99 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 137 (accept_3_2 10 99 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 137 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 99 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 99 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 99 137 (accept_3_2 7 99 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99
  137 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 99 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 99 137 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 99 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 137 (accept_3_2 4 99 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 99 137 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 99 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 99
  137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 137 (accept_3_2 1 99 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99 137))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 98 137
  (Eq.refl Bool.true) (allA_succ_of_accept 39 98 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 98 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 98 137
  (Polychromatic418967fa.accept_16_6_2_9_1_5897 38 98 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 98 137 (accept_3_2 37 98 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  98 137 (Polychromatic418967fa.accept_15_6_8_2_1_104 36 98 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 98 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 98 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 98 137 (accept_3_2 34 98 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 98 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 98 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 98 137
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 98 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 98 137 (accept_3_2 31 98 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  98 137 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 98 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 98 137 (Polychromatic418967fa.accept_10_9_8_7_1_714 29 98 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 98 137 (accept_3_2 28 98 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 98 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 98 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 98 137
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 26 98 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 98 137 (accept_3_2 25 98 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  98 137 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 98 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 98 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 98 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 98 137 (accept_3_2 22 98 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 98 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 98 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 98 137
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 98 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 98 137 (accept_3_2 19 98 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  98 137 (Polychromatic418967fa.accept_19_18_3_4_1_7079 18 98 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 98 137 (Polychromatic418967fa.accept_11_6_10_5_1_341 17 98 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 98 137 (accept_3_2 16 98 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 98 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 98 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 98 137
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 98 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 98 137 (accept_3_2 13 98 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  98 137 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 98 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 98 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 98 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 98 137 (accept_3_2 10 98 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 98 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 98 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 98 137
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 98 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 98 137 (accept_3_2 7 98 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 98
  137 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 98 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 98 137 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 98 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 98 137 (accept_3_2 4 98 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 98 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 98 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 98 137 (Polychromatic418967fa.accept_17_2_13_1_1_3355
  2 98 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 98 137 (accept_3_2 1 98
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98 137)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41
  97 137 (Eq.refl Bool.true) (allA_of_3_0 41 97 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 96 137
  (Eq.refl Bool.true) (allA_succ_of_accept 41 96 137 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 96 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 96 137 (accept_3_2 40 96 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 96 137 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 96 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 96 137
  (Polychromatic418967fa.accept_13_12_5_7_1_1696 38 96 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 96 137 (accept_3_2 37 96 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  96 137 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 96 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 96 137 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 96 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 96 137 (accept_3_2 34 96 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 96 137 (Polychromatic418967fa.accept_10_3_6_7_1_2188 33 96 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 96 137
  (Polychromatic418967fa.accept_9_5_6_2_1_161 32 96 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 96 137 (accept_3_2 31 96 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  96 137 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 96 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 96 137 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 96 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 96 137 (accept_3_2 28 96 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 96 137 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 96 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 96 137
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 96 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 96 137 (accept_3_2 25 96 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  96 137 (Polychromatic418967fa.accept_11_2_8_5_1_1219 24 96 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 96 137 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 96 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 96 137 (accept_3_2 22 96 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 96 137 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 96 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 96 137
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 96 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 96 137 (accept_3_2 19 96 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  96 137 (Polychromatic418967fa.accept_21_18_12_11_1_7078 18 96 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 96 137 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 96 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 96 137 (accept_3_2 16 96 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 96 137 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 96 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 96 137
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 96 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 96 137 (accept_3_2 13 96 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  96 137 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 96 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 96 137 (Polychromatic418967fa.accept_10_1_6_7_1_710 11 96 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 96 137 (accept_3_2 10 96 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 96 137 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 96 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 96 137
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 96 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 96 137 (accept_3_2 7 96 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 96
  137 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 96 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 96 137 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 96 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 96 137 (accept_3_2 4 96 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 96 137 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 96 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 96 137 (Polychromatic418967fa.accept_7_2_5_4_1_115 2
  96 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 96 137 (accept_3_2 1 96 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96 137)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 95
  137 (Eq.refl Bool.true) (allA_succ_of_accept 42 95 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 95 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 137
  (Polychromatic418967fa.accept_15_11_5_2_1_520 41 95 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 95 137 (accept_3_2 40 95 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  95 137 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 95 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 95 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 95 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 137 (accept_3_2 37 95 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 137 (Polychromatic418967fa.accept_13_10_4_7_1_2465 36 95 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 95 137
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 95 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 95 137 (accept_3_2 34 95 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  95 137 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 95 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 95 137 (Polychromatic418967fa.accept_10_2_5_7_1_1124 32 95 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 137 (accept_3_2 31 95 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 95 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 95 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 95 137
  (Polychromatic418967fa.accept_13_3_4_7_1_1711 29 95 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 95 137 (accept_3_2 28 95 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  95 137 (Polychromatic418967fa.accept_15_12_5_2_1_2786 27 95 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 95 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 95 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 137 (accept_3_2 25 95 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 95 137 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 95 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 137
  (Polychromatic418967fa.accept_10_3_5_7_1_330 23 95 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 95 137 (accept_3_2 22 95 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  95 137 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 95 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 95 137 (Polychromatic418967fa.accept_11_9_7_5_1_749 20 95 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 137 (accept_3_2 19 95 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 95 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 137
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 95 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 137 (accept_3_2 16 95 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  95 137 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 95 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 95 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 95 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 137 (accept_3_2 13 95 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 137 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 95 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 137
  (Polychromatic418967fa.accept_13_11_4_7_1_2419 11 95 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 95 137 (accept_3_2 10 95 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  95 137 (Polychromatic418967fa.accept_11_9_7_5_1_749 9 95 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 95 137 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 95 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 137 (accept_3_2 7 95 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 95 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 137
  (Polychromatic418967fa.accept_20_5_15_17_1_7077 5 95 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 95 137 (accept_3_2 4 95 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95
  137 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 95 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 95 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 95 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 137 (accept_3_2 1 95 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 95 137))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 94 137 (Eq.refl Bool.true)
  (allA_of_3_0 44 94 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 93 137 (Eq.refl Bool.true)
  (allA_succ_of_accept 44 93 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 93 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 93 137 (accept_3_2 43 93 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 93 137 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 93 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 93 137 (Polychromatic418967fa.accept_7_6_2_4_1_291 41
  93 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 137 (accept_3_2 40 93
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 137
  (Polychromatic418967fa.accept_12_3_9_5_1_853 39 93 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 93 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 93 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 93 137 (accept_3_2 37 93 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 93 137 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 93 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 93 137 (Polychromatic418967fa.accept_9_8_3_2_1_417 35
  93 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 137 (accept_3_2 34 93
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 137
  (Polychromatic418967fa.accept_7_5_2_4_1_126 33 93 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 93 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 93 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 93 137 (accept_3_2 31 93 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 93 137 (Polychromatic418967fa.accept_14_2_9_11_1_3054 30 93 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 93 137
  (Polychromatic418967fa.accept_15_14_3_2_1_2811 29 93 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 93 137 (accept_3_2 28 93 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  93 137 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 93 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 93 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 93 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 93 137 (accept_3_2 25 93 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 93 137 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 93 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 93 137
  (Polychromatic418967fa.accept_9_5_3_2_1_171 23 93 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 93 137 (accept_3_2 22 93 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  93 137 (Polychromatic418967fa.accept_13_8_2_7_1_2452 21 93 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 93 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 93 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 137 (accept_3_2 19 93 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 93 137 (Polychromatic418967fa.accept_13_5_2_7_1_2414 18 93 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 137
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 93 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 93 137 (accept_3_2 16 93 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  93 137 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 93 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 93 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 93 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 137 (accept_3_2 13 93 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 93 137 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 93 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 137
  (Polychromatic418967fa.accept_17_11_8_1_1_3362 11 93 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 93 137 (accept_3_2 10 93 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  93 137 (Polychromatic418967fa.accept_13_9_2_7_1_1083 9 93 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 93 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 93 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 137 (accept_3_2 7 93 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 93 137 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 93 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 137
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 93 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 93 137 (accept_3_2 4 93 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93
  137 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 93 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 93 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 93 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 137 (accept_3_2 1 93 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 93 137))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 92 137 (Eq.refl Bool.true)
  (allA_succ_of_accept 45 92 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 92 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 92 137 (Polychromatic418967fa.accept_10_4_2_7_1_373 44 92 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 92 137 (accept_3_2 43 92 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 92 137 (Polychromatic418967fa.accept_13_3_1_7_1_1706
  42 92 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 92 137
  (Polychromatic418967fa.accept_19_3_16_4_1_7076 41 92 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 92 137 (accept_3_2 40 92 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  92 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 92 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 92 137 (Polychromatic418967fa.accept_7_3_1_4_1_121 38 92 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 92 137 (accept_3_2 37 92 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 92 137 (Polychromatic418967fa.accept_16_4_12_9_1_2567 36 92 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 92 137
  (Polychromatic418967fa.accept_10_5_2_7_1_345 35 92 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 92 137 (accept_3_2 34 92 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  92 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 92 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 92 137 (Polychromatic418967fa.accept_11_10_4_5_1_359 32 92 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 92 137 (accept_3_2 31 92 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 92 137 (Polychromatic418967fa.accept_19_11_16_4_1_7075 30 92 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 92 137
  (Polychromatic418967fa.accept_8_5_4_1_1_111 29 92 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 92 137 (accept_3_2 28 92 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  92 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 92 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 92 137 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 92 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 92 137 (accept_3_2 25 92 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 92 137 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 92 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 92 137
  (Polychromatic418967fa.accept_22_1_4_5_1_7074 23 92 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 92 137 (accept_3_2 22 92 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  92 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 92 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 92 137 (Polychromatic418967fa.accept_16_4_12_9_1_2567 20 92 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 92 137 (accept_3_2 19 92 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 92 137 (Polychromatic418967fa.accept_14_4_8_11_1_794 18 92 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 92 137
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 92 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 92 137 (accept_3_2 16 92 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  92 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 92 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 92 137 (Polychromatic418967fa.accept_10_4_2_7_1_373 14 92 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 92 137 (accept_3_2 13 92 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 92 137 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 92 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 92 137
  (Polychromatic418967fa.accept_13_11_1_7_1_1691 11 92 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 92 137 (accept_3_2 10 92 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  92 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 92 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 92 137 (Polychromatic418967fa.accept_13_8_1_7_1_2505 8 92 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 92 137 (accept_3_2 7 92 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 92 137 (Polychromatic418967fa.accept_13_6_1_7_1_1690 6 92 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 92 137
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 92 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 92 137 (accept_3_2 4 92 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 92
  137 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 92 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 92 137 (Polychromatic418967fa.accept_12_2_8_5_1_408 2 92 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 137 (accept_3_2 1 92 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 92 137)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 91 137 (Eq.refl Bool.true)
  (allA_of_3_0 47 91 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 90 137 (Eq.refl Bool.true)
  (allA_succ_of_accept 47 90 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 90 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 90 137 (accept_3_2 46 90 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 90 137 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 90 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 90 137 (Polychromatic418967fa.accept_7_2_6_4_1_29 44
  90 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 90 137 (accept_3_2 43 90
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 90 137
  (Polychromatic418967fa.accept_27_15_9_2_1_7073 42 90 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 90 137 (Polychromatic418967fa.accept_11_8_2_5_1_1769 41 90 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 90 137 (accept_3_2 40 90 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 90 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 90 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 90 137 (Polychromatic418967fa.accept_7_3_6_4_1_30 38
  90 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 137 (accept_3_2 37 90
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 90 137
  (Polychromatic418967fa.accept_13_10_12_7_1_1079 36 90 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 90 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 90 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 90 137 (accept_3_2 34 90 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 90 137 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 90 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 90 137 (Polychromatic418967fa.accept_13_6_12_7_1_5131
  32 90 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 90 137 (accept_3_2 31
  90 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 90 137
  (Polychromatic418967fa.accept_7_2_6_4_1_29 30 90 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 90 137 (Polychromatic418967fa.accept_19_10_14_4_1_7072 29 90 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 90 137 (accept_3_2 28 90 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 90 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 90 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 90 137 (Polychromatic418967fa.accept_7_5_6_4_1_117 26
  90 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 90 137 (accept_3_2 25 90
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 90 137 (Polychromatic418967fa.accept_7_3_6_4_1_30
  24 90 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 90 137
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 90 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 90 137 (accept_3_2 22 90 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  90 137 (Polychromatic418967fa.accept_13_8_12_7_1_2442 21 90 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 90 137 (Polychromatic418967fa.accept_21_20_6_11_1_2623 20 90 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 90 137 (accept_3_2 19 90 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 90 137 (Polychromatic418967fa.accept_13_5_12_7_1_1080 18 90
  137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 90 137
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 90 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 90 137 (accept_3_2 16 90 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  90 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 90 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 90 137 (Polychromatic418967fa.accept_21_14_6_11_1_7071 14 90 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 90 137 (accept_3_2 13 90 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 90 137 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 90 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 90 137
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 90 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 90 137 (accept_3_2 10 90 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  90 137 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 90 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 90 137 (Polychromatic418967fa.accept_11_8_2_5_1_1769 8 90 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 137 (accept_3_2 7 90 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 90 137 (Polychromatic418967fa.accept_13_6_12_7_1_5131 6 90 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 90 137
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 90 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 90 137 (accept_3_2 4 90 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 90
  137 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 90 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 90 137 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 90 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 90 137 (accept_3_2 1 90 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 90 137)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 89 137 (Eq.refl Bool.true)
  (allA_succ_of_accept 48 89 137 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 89 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 137 (Polychromatic418967fa.accept_19_9_13_4_1_2982 47 89
  137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 89 137 (accept_3_2 46 89 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 89 137 (Polychromatic418967fa.accept_19_7_13_4_1_1824
  45 89 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 89 137
  (Polychromatic418967fa.accept_7_2_5_4_1_115 44 89 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 89 137 (accept_3_2 43 89 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  89 137 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 89 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 89 137 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 89 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 89 137 (accept_3_2 40 89 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 89 137 (Polychromatic418967fa.accept_9_3_8_2_1_162 39 89 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 89 137
  (Polychromatic418967fa.accept_10_8_9_7_1_1118 38 89 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 89 137 (accept_3_2 37 89 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  89 137 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 89 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 89 137 (Polychromatic418967fa.accept_13_9_11_7_1_1077 35 89 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 89 137 (accept_3_2 34 89 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 89 137 (Polychromatic418967fa.accept_9_6_8_2_1_410 33 89 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 89 137
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 89 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 89 137 (accept_3_2 31 89 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  89 137 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 89 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 89 137 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 89 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 89 137 (accept_3_2 28 89 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 89 137 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 89 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 89 137
  (Polychromatic418967fa.accept_19_7_13_4_1_1824 26 89 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 89 137 (accept_3_2 25 89 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  89 137 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 89 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 89 137 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 89 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 89 137 (accept_3_2 22 89 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 89 137 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 89 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 89 137
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 89 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 89 137 (accept_3_2 19 89 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  89 137 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 89 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 89 137 (Polychromatic418967fa.accept_11_6_1_5_1_2388 17 89 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 89 137 (accept_3_2 16 89 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 89 137 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 89 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 89 137
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 89 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 89 137 (accept_3_2 13 89 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  89 137 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 89 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 89 137 (Polychromatic418967fa.accept_23_11_20_22_1_7070 11 89 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 89 137 (accept_3_2 10 89 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 89 137 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 89 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 89 137
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 89 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 89 137 (accept_3_2 7 89 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 89
  137 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 89 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 89 137 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 89 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 89 137 (accept_3_2 4 89 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 89 137 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 89 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 89 137 (Polychromatic418967fa.accept_7_2_5_4_1_115 2
  89 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 137 (accept_3_2 1 89 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 89 137))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  50 88 137 (Eq.refl Bool.true) (allA_of_3_0 50 88 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 87 137
  (Eq.refl Bool.true) (allA_succ_of_accept 50 87 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 87 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 137 (accept_3_2 49 87 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 87 137 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 87 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 87 137
  (Polychromatic418967fa.accept_13_8_9_7_1_530 47 87 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 87 137 (accept_3_2 46 87 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  87 137 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 87 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 87 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 87 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 87 137 (accept_3_2 43 87 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 87 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 87 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 87 137
  (Polychromatic418967fa.accept_7_6_3_4_1_294 41 87 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 87 137 (accept_3_2 40 87 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  87 137 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 87 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 87 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 87 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 87 137 (accept_3_2 37 87 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 87 137 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 87 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 87 137
  (Polychromatic418967fa.accept_9_8_6_2_1_744 35 87 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 87 137 (accept_3_2 34 87 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  87 137 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 87 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 87 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 87 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 137 (accept_3_2 31 87 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 87 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 87 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 137
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 87 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 87 137 (accept_3_2 28 87 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  87 137 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 87 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 87 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 87 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 137 (accept_3_2 25 87 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 87 137 (Polychromatic418967fa.accept_13_11_9_7_1_2484 24 87 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 137
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 87 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 87 137 (accept_3_2 22 87 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  87 137 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 87 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 87 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 87 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 137 (accept_3_2 19 87 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 87 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 87 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 137
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 87 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 87 137 (accept_3_2 16 87 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  87 137 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 87 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 87 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 87 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 137 (accept_3_2 13 87 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 87 137 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 87 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 137
  (Polychromatic418967fa.accept_13_11_9_7_1_2484 11 87 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 87 137 (accept_3_2 10 87 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  87 137 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 87 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 87 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 87 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 137 (accept_3_2 7 87 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 87 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 87 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 137
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 87 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 87 137 (accept_3_2 4 87 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87
  137 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 87 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 87 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 87 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 137 (accept_3_2 1 87 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 87 137))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 86 137 (Eq.refl
  Bool.true) (allA_succ_of_accept 51 86 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 86 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 86 137 (Polychromatic418967fa.accept_15_5_11_2_1_1095
  50 86 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 86 137 (accept_3_2 49
  86 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 86 137
  (Polychromatic418967fa.accept_7_6_2_4_1_291 48 86 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 86 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 86 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 86 137 (accept_3_2 46 86 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 86 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 86 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 86 137 (Polychromatic418967fa.accept_9_8_5_2_1_422 44
  86 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 86 137 (accept_3_2 43 86
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 86 137
  (Polychromatic418967fa.accept_9_6_5_2_1_421 42 86 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 86 137 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 86 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 86 137 (accept_3_2 40 86 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 86 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 86 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 86 137 (Polychromatic418967fa.accept_13_12_8_7_1_2526
  38 86 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 86 137 (accept_3_2 37
  86 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 86 137
  (Polychromatic418967fa.accept_13_10_8_7_1_1074 36 86 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 86 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 86 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 86 137 (accept_3_2 34 86 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 86 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 86 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 86 137 (Polychromatic418967fa.accept_12_8_2_5_1_844
  32 86 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 86 137 (accept_3_2 31
  86 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 86 137
  (Polychromatic418967fa.accept_9_3_5_2_1_28 30 86 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 86 137 (Polychromatic418967fa.accept_11_7_9_5_1_338 29 86 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 86 137 (accept_3_2 28 86 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 86 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 86 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 86 137 (Polychromatic418967fa.accept_7_5_2_4_1_126 26
  86 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 86 137 (accept_3_2 25 86
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 86 137
  (Polychromatic418967fa.accept_9_6_5_2_1_421 24 86 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 86 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 86 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 86 137 (accept_3_2 22 86 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 86 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 86 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 86 137 (Polychromatic418967fa.accept_7_6_2_4_1_291 20
  86 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 86 137 (accept_3_2 19 86
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 86 137
  (Polychromatic418967fa.accept_11_7_9_5_1_338 18 86 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 86 137 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 86 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 86 137 (accept_3_2 16 86 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 86 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 86 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 86 137 (Polychromatic418967fa.accept_13_1_8_7_1_1088
  14 86 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 86 137 (accept_3_2 13
  86 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 86 137
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 86 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 86 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 86 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 86 137 (accept_3_2 10 86 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 86 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 86 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 137 (Polychromatic418967fa.accept_9_8_5_2_1_422 8
  86 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 86 137 (accept_3_2 7 86 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86 137 (Polychromatic418967fa.accept_7_6_2_4_1_291 6
  86 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 86 137
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 86 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 86 137 (accept_3_2 4 86 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 86
  137 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 86 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 86 137 (Polychromatic418967fa.accept_13_2_8_7_1_2424 2 86 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 86 137 (accept_3_2 1 86 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 86 137)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 85 137 (Eq.refl
  Bool.true) (allA_of_3_0 53 85 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 54 84 137 (Eq.refl Bool.true)
  (allA_succ_of_accept 53 84 137 (Polychromatic418967fa.accept_8_5_4_1_1_111 53 84 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 84 137 (accept_3_2 52 84 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 84 137 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 84 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 84 137 (Polychromatic418967fa.accept_9_5_3_2_1_171 50
  84 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 84 137 (accept_3_2 49 84
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 84 137
  (Polychromatic418967fa.accept_13_9_6_7_1_551 48 84 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 84 137 (Polychromatic418967fa.accept_19_9_8_4_1_7046 47 84 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 84 137 (accept_3_2 46 84 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 84 137 (Polychromatic418967fa.accept_8_5_4_1_1_111 45 84 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 84 137 (Polychromatic418967fa.accept_9_8_3_2_1_417 44
  84 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 84 137 (accept_3_2 43 84
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 84 137
  (Polychromatic418967fa.accept_9_6_3_2_1_431 42 84 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 84 137 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 84 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 84 137 (accept_3_2 40 84 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 84 137 (Polychromatic418967fa.accept_17_5_16_1_1_3358 39 84 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 84 137
  (Polychromatic418967fa.accept_13_12_6_7_1_1071 38 84 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 84 137 (accept_3_2 37 84 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  84 137 (Polychromatic418967fa.accept_17_2_16_1_1_2260 36 84 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 84 137 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 84 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 84 137 (accept_3_2 34 84 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 84 137 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 84 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 84 137
  (Polychromatic418967fa.accept_9_5_3_2_1_171 32 84 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 84 137 (accept_3_2 31 84 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  84 137 (Polychromatic418967fa.accept_13_4_6_7_1_2471 30 84 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 84 137 (Polychromatic418967fa.accept_8_5_4_1_1_111 29 84 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 84 137 (accept_3_2 28 84 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 84 137 (Polychromatic418967fa.accept_13_1_6_7_1_550 27 84 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 84 137
  (Polychromatic418967fa.accept_9_8_3_2_1_417 26 84 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 84 137 (accept_3_2 25 84 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  84 137 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 84 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 84 137 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 84 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 84 137 (accept_3_2 22 84 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 84 137 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 84 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 84 137
  (Polychromatic418967fa.accept_11_9_7_5_1_749 20 84 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 84 137 (accept_3_2 19 84 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  84 137 (Polychromatic418967fa.accept_19_18_8_4_1_7069 18 84 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 84 137 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 84 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 84 137 (accept_3_2 16 84 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 84 137 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 84 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 84 137
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 84 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 84 137 (accept_3_2 13 84 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  84 137 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 84 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 84 137 (Polychromatic418967fa.accept_10_1_4_7_1_374 11 84 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 84 137 (accept_3_2 10 84 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 84 137 (Polychromatic418967fa.accept_11_9_7_5_1_749 9 84 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 84 137
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 84 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 84 137 (accept_3_2 7 84 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 84
  137 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 84 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 84 137 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 84 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 84 137 (accept_3_2 4 84 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 84 137 (Polychromatic418967fa.accept_10_3_4_7_1_353 3 84 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 84 137 (Polychromatic418967fa.accept_10_2_4_7_1_352 2
  84 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 137 (accept_3_2 1 84 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84 137))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 55 83 137 (Eq.refl Bool.true) (allA_succ_of_accept 54 83 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 54
  83 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 137
  (Polychromatic418967fa.accept_24_5_11_17_1_7068 53 83 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 137 (accept_3_2 52 83 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 137 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 83 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 83 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 137 (accept_3_2 49 83 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 137 (Polychromatic418967fa.accept_21_6_20_11_1_7067 48 83 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 137
  (Polychromatic418967fa.accept_7_5_6_4_1_117 47 83 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 137 (accept_3_2 46 83 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 137 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 83 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 137 (Polychromatic418967fa.accept_7_2_6_4_1_29 44 83 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 137 (accept_3_2 43 83 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 83 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 137
  (Polychromatic418967fa.accept_13_2_5_7_1_1695 41 83 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 137 (accept_3_2 40 83 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 137 (Polychromatic418967fa.accept_15_9_8_2_1_1109 39 83 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 83 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 137 (accept_3_2 37 83 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 137 (Polychromatic418967fa.accept_10_6_3_7_1_2197 36 83 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 137
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 35 83 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 137 (accept_3_2 34 83 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 137 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 83 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 137 (Polychromatic418967fa.accept_11_10_6_5_1_1239 32 83 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 137 (accept_3_2 31 83 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 83 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 137
  (Polychromatic418967fa.accept_17_12_15_1_1_5798 29 83 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 137 (accept_3_2 28 83 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 137 (Polychromatic418967fa.accept_21_6_20_11_1_7067 27 83 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 83 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 137 (accept_3_2 25 83 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 137 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 83 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 137
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 83 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 137 (accept_3_2 22 83 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 137 (Polychromatic418967fa.accept_11_10_6_5_1_1239 21 83 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 137 (Polychromatic418967fa.accept_17_3_15_1_1_3348 20 83 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 137 (accept_3_2 19 83 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 83 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 137
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 83 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 137 (accept_3_2 16 83 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 137 (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 83 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 83 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 137 (accept_3_2 13 83 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 137 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 83 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 137
  (Polychromatic418967fa.accept_13_11_5_7_1_2420 11 83 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 137 (accept_3_2 10 83 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 137 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 83 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 137 (Polychromatic418967fa.accept_21_8_20_11_1_7025 8 83 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 137 (accept_3_2 7 83 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 83 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 137
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 83 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 137 (accept_3_2 4 83 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  137 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 83 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 83 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 83 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 137 (accept_3_2 1 83 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 137))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 82 137 (Eq.refl
  Bool.true) (allA_of_3_0 56 82 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 57 81 137 (Eq.refl Bool.true)
  (allA_succ_of_accept 56 81 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 81 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 137 (accept_3_2 55 81 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 81 137 (Polychromatic418967fa.accept_10_4_1_7_1_371 54 81 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 137 (Polychromatic418967fa.accept_13_1_3_7_1_1710
  53 81 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 137 (accept_3_2 52
  81 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 137
  (Polychromatic418967fa.accept_12_3_9_5_1_853 51 81 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 81 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 81 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 81 137 (accept_3_2 49 81 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 81 137 (Polychromatic418967fa.accept_13_9_3_7_1_1065 48 81 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 137 (Polychromatic418967fa.accept_13_8_3_7_1_2455
  47 81 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 137 (accept_3_2 46
  81 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 137
  (Polychromatic418967fa.accept_16_13_1_9_1_2597 45 81 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 81 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 81 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 137 (accept_3_2 43 81 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 81 137 (Polychromatic418967fa.accept_15_12_6_2_1_2760 42 81 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 137
  (Polychromatic418967fa.accept_15_11_6_2_1_1106 41 81 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 81 137 (accept_3_2 40 81 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  81 137 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 81 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 81 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 81 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 137 (accept_3_2 37 81 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 81 137 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 81 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 137
  (Polychromatic418967fa.accept_13_9_3_7_1_1065 35 81 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 81 137 (accept_3_2 34 81 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  81 137 (Polychromatic418967fa.accept_18_15_9_11_1_4371 33 81 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 81 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 81 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 137 (accept_3_2 31 81 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 81 137 (Polychromatic418967fa.accept_13_4_3_7_1_2515 30 81 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 137
  (Polychromatic418967fa.accept_16_13_1_9_1_2597 29 81 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 81 137 (accept_3_2 28 81 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  81 137 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 81 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 81 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 81 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 137 (accept_3_2 25 81 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 81 137 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 81 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 137
  (Polychromatic418967fa.accept_13_10_3_7_1_2517 23 81 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 137 (accept_3_2 22 81 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  81 137 (Polychromatic418967fa.accept_11_10_4_5_1_359 21 81 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 81 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 81 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 137 (accept_3_2 19 81 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 81 137 (Polychromatic418967fa.accept_16_2_1_9_1_2577 18 81 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 137
  (Polychromatic418967fa.accept_13_4_3_7_1_2515 17 81 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 81 137 (accept_3_2 16 81 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  81 137 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 81 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 81 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 81 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 137 (accept_3_2 13 81 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 81 137 (Polychromatic418967fa.accept_15_12_6_2_1_2760 12 81 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 137
  (Polychromatic418967fa.accept_13_11_3_7_1_2513 11 81 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 81 137 (accept_3_2 10 81 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  81 137 (Polychromatic418967fa.accept_13_9_3_7_1_1065 9 81 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 81 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 81 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 137 (accept_3_2 7 81 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 137 (Polychromatic418967fa.accept_10_6_1_7_1_342 6 81 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 137
  (Polychromatic418967fa.accept_16_5_1_9_1_4621 5 81 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 137 (accept_3_2 4 81 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81
  137 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 81 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 81 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 81 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 137 (accept_3_2 1 81 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 81 137))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 80 137 (Eq.refl
  Bool.true) (allA_succ_of_accept 57 80 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 80 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 80 137 (Polychromatic418967fa.accept_15_11_5_2_1_520
  56 80 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 80 137 (accept_3_2 55
  80 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 80 137
  (Polychromatic418967fa.accept_23_8_11_22_1_7066 54 80 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 80 137 (Polychromatic418967fa.accept_22_9_14_5_1_7065 53 80 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 80 137 (accept_3_2 52 80 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 80 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 80 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 80 137 (Polychromatic418967fa.accept_7_1_3_4_1_128 50
  80 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 80 137 (accept_3_2 49 80
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 80 137
  (Polychromatic418967fa.accept_7_6_3_4_1_294 48 80 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 80 137 (Polychromatic418967fa.accept_13_8_2_7_1_2452 47 80 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 80 137 (accept_3_2 46 80 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 80 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 80 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 80 137 (Polychromatic418967fa.accept_13_5_2_7_1_2414
  44 80 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 80 137 (accept_3_2 43
  80 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 80 137
  (Polychromatic418967fa.accept_9_6_8_2_1_410 42 80 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 80 137 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 80 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 80 137 (accept_3_2 40 80 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 80 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 80 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 80 137 (Polychromatic418967fa.accept_12_2_8_5_1_408
  38 80 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 80 137 (accept_3_2 37
  80 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 80 137
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 80 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 80 137 (Polychromatic418967fa.accept_13_9_2_7_1_1083 35 80 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 80 137 (accept_3_2 34 80 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 80 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 80 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 80 137 (Polychromatic418967fa.accept_9_5_8_2_1_409 32
  80 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 80 137 (accept_3_2 31 80
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 80 137
  (Polychromatic418967fa.accept_9_3_8_2_1_162 30 80 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 80 137 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 80 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 80 137 (accept_3_2 28 80 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 80 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 80 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 80 137 (Polychromatic418967fa.accept_12_2_8_5_1_408
  26 80 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 80 137 (accept_3_2 25
  80 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 80 137
  (Polychromatic418967fa.accept_9_6_8_2_1_410 24 80 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 80 137 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 80 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 80 137 (accept_3_2 22 80 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 80 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 80 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 80 137 (Polychromatic418967fa.accept_7_6_3_4_1_294 20
  80 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 80 137 (accept_3_2 19 80
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 80 137
  (Polychromatic418967fa.accept_13_5_2_7_1_2414 18 80 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 80 137 (Polychromatic418967fa.accept_22_17_14_5_1_7064 17 80 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 80 137 (accept_3_2 16 80 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 80 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 80 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 80 137 (Polychromatic418967fa.accept_9_5_8_2_1_409 14
  80 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 80 137 (accept_3_2 13 80
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 80 137
  (Polychromatic418967fa.accept_9_3_8_2_1_162 12 80 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 80 137 (Polychromatic418967fa.accept_15_11_5_2_1_520 11 80 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 80 137 (accept_3_2 10 80 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 80 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 80 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 80 137 (Polychromatic418967fa.accept_7_1_3_4_1_128 8
  80 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 80 137 (accept_3_2 7 80 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 80 137 (Polychromatic418967fa.accept_7_6_3_4_1_294 6
  80 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 80 137
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 80 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 80 137 (accept_3_2 4 80 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 80
  137 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 80 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 80 137 (Polychromatic418967fa.accept_12_2_8_5_1_408 2 80 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 80 137 (accept_3_2 1 80 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 80 137)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 79 137 (Eq.refl
  Bool.true) (allA_of_3_0 59 79 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 78 137 (Eq.refl Bool.true)
  (allA_succ_of_accept 59 78 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 78 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 78 137 (accept_3_2 58 78 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 78 137 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 78 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 78 137 (Polychromatic418967fa.accept_19_18_2_4_1_7039
  56 78 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 78 137 (accept_3_2 55
  78 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 78 137
  (Polychromatic418967fa.accept_7_5_1_4_1_122 54 78 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 78 137 (Polychromatic418967fa.accept_9_8_6_2_1_744 53 78 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 78 137 (accept_3_2 52 78 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 78 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 78 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 78 137 (Polychromatic418967fa.accept_9_5_6_2_1_161 50
  78 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 137 (accept_3_2 49 78
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 78 137
  (Polychromatic418967fa.accept_9_3_6_2_1_160 48 78 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 78 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 78 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 78 137 (accept_3_2 46 78 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 78 137 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 78 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 78 137 (Polychromatic418967fa.accept_9_8_6_2_1_744 44
  78 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 137 (accept_3_2 43 78
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 78 137
  (Polychromatic418967fa.accept_15_12_3_2_1_2756 42 78 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 78 137 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 78 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 78 137 (accept_3_2 40 78 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 78 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 78 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 78 137 (Polychromatic418967fa.accept_7_3_1_4_1_121 38
  78 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 78 137 (accept_3_2 37 78
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 78 137
  (Polychromatic418967fa.accept_16_4_14_9_1_4657 36 78 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 78 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 78 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 78 137 (accept_3_2 34 78 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 78 137 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 78 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 78 137 (Polychromatic418967fa.accept_9_5_6_2_1_161 32
  78 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 137 (accept_3_2 31 78
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 78 137
  (Polychromatic418967fa.accept_9_3_6_2_1_160 30 78 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 78 137 (Polychromatic418967fa.accept_10_9_8_7_1_714 29 78 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 78 137 (accept_3_2 28 78 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 78 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 78 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 78 137 (Polychromatic418967fa.accept_7_5_1_4_1_122 26
  78 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 137 (accept_3_2 25 78
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 78 137
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 78 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 78 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 78 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 78 137 (accept_3_2 22 78 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 78 137 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 78 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 78 137 (Polychromatic418967fa.accept_15_5_3_2_1_5930
  20 78 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 137 (accept_3_2 19
  78 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 137
  (Polychromatic418967fa.accept_14_4_8_11_1_794 18 78 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 78 137 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 78 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 78 137 (accept_3_2 16 78 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 78 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 78 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 78 137 (Polychromatic418967fa.accept_9_5_6_2_1_161 14
  78 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 137 (accept_3_2 13 78
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 78 137
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 78 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 78 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 78 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 78 137 (accept_3_2 10 78 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 78 137 (Polychromatic418967fa.accept_10_9_8_7_1_714 9 78 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 78 137 (Polychromatic418967fa.accept_9_8_6_2_1_744 8
  78 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 137 (accept_3_2 7 78 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 78 137 (Polychromatic418967fa.accept_11_6_1_5_1_2388 6
  78 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 78 137
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 78 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 78 137 (accept_3_2 4 78 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 78
  137 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 78 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 78 137 (Polychromatic418967fa.accept_20_2_18_17_1_7063 2 78 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 78 137 (accept_3_2 1 78 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 78 137)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 77 137
  (Eq.refl Bool.true) (allA_succ_of_accept 60 77 137 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 77 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 137
  (Polychromatic418967fa.accept_14_3_7_11_1_765 59 77 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 77 137 (accept_3_2 58 77 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 137 (Polychromatic418967fa.accept_9_3_5_2_1_28 57 77 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 137 (Polychromatic418967fa.accept_13_4_12_7_1_2439 56 77 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 137 (accept_3_2 55 77 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 137 (Polychromatic418967fa.accept_16_6_13_9_1_4690 54 77
  137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 137
  (Polychromatic418967fa.accept_9_8_5_2_1_422 53 77 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 137 (accept_3_2 52 77 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 137 (Polychromatic418967fa.accept_9_6_5_2_1_421 51 77 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 137 (Polychromatic418967fa.accept_13_11_12_7_1_2443 50 77 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 137 (accept_3_2 49 77 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 137 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 77 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 137
  (Polychromatic418967fa.accept_13_8_12_7_1_2442 47 77 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 137 (accept_3_2 46 77 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 137 (Polychromatic418967fa.accept_13_6_12_7_1_5131 45 77 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 137 (Polychromatic418967fa.accept_8_4_5_1_1_299 44 77 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 137 (accept_3_2 43 77 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 137 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 77 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 137
  (Polychromatic418967fa.accept_19_3_1_4_1_1860 41 77 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 137 (accept_3_2 40 77 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 137 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 77 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 137 (Polychromatic418967fa.accept_14_10_7_11_1_3015 38 77 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 137 (accept_3_2 37 77 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 137 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 77 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 137
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 77 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 137 (accept_3_2 34 77 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 137 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 77 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 137 (Polychromatic418967fa.accept_13_6_12_7_1_5131 32 77 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 137 (accept_3_2 31 77 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 137 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 77 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 137
  (Polychromatic418967fa.accept_19_10_1_4_1_4237 29 77 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 137 (accept_3_2 28 77 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 137 (Polychromatic418967fa.accept_17_10_9_1_1_7062 27 77 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 137 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 77 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 137 (accept_3_2 25 77 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 137 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 77 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 137
  (Polychromatic418967fa.accept_13_10_12_7_1_1079 23 77 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 137 (accept_3_2 22 77 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 137 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 77 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 137 (Polychromatic418967fa.accept_8_4_5_1_1_299 20 77 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 137 (accept_3_2 19 77 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 137 (Polychromatic418967fa.accept_13_5_12_7_1_1080 18 77 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 137
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 77 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 137 (accept_3_2 16 77 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 137 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 77 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 137 (Polychromatic418967fa.accept_18_14_5_11_1_5676 14 77 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 137 (accept_3_2 13 77 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 137 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 77 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 137
  (Polychromatic418967fa.accept_13_11_12_7_1_2443 11 77 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 137 (accept_3_2 10 77 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 137 (Polychromatic418967fa.accept_22_9_11_5_1_7061 9 77 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 137 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 77 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 137 (accept_3_2 7 77 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 137 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 77 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 137
  (Polychromatic418967fa.accept_13_5_12_7_1_1080 5 77 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 137 (accept_3_2 4 77 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  137 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 77 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 137 (Polychromatic418967fa.accept_21_2_14_11_1_7060 2 77 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 137 (accept_3_2 1 77 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 137))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 76 137
  (Eq.refl Bool.true) (allA_of_3_0 62 76 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 63 75 137 (Eq.refl
  Bool.true) (allA_succ_of_accept 62 75 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 75 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 75 137 (accept_3_2 61 75 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 75 137 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 75 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 75 137
  (Polychromatic418967fa.accept_9_5_3_2_1_171 59 75 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 75 137 (accept_3_2 58 75 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  75 137 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 75 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 75 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 75 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 75 137 (accept_3_2 55 75 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 75 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 75 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 75 137
  (Polychromatic418967fa.accept_9_8_3_2_1_417 53 75 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 75 137 (accept_3_2 52 75 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  75 137 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 75 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 75 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 75 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 75 137 (accept_3_2 49 75 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 75 137 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 75 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 75 137
  (Polychromatic418967fa.accept_13_8_10_7_1_1702 47 75 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 75 137 (accept_3_2 46 75 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  75 137 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 75 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 75 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 75 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 137 (accept_3_2 43 75 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 75 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 75 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 75 137
  (Polychromatic418967fa.accept_7_6_5_4_1_297 41 75 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 75 137 (accept_3_2 40 75 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  75 137 (Polychromatic418967fa.accept_20_19_15_17_1_7059 39 75 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 75 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 75 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 137 (accept_3_2 37 75 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 75 137 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 75 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 75 137
  (Polychromatic418967fa.accept_9_8_3_2_1_417 35 75 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 75 137 (accept_3_2 34 75 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  75 137 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 75 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 75 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 75 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 137 (accept_3_2 31 75 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 75 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 75 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 75 137
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 75 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 75 137 (accept_3_2 28 75 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  75 137 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 75 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 75 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 75 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 137 (accept_3_2 25 75 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 75 137 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 75 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 75 137
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 75 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 75 137 (accept_3_2 22 75 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  75 137 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 75 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 75 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 75 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 137 (accept_3_2 19 75 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 75 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 137
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 75 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 75 137 (accept_3_2 16 75 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  75 137 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 75 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 75 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 75 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 137 (accept_3_2 13 75 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 75 137 (Polychromatic418967fa.accept_10_2_5_7_1_1124 12 75 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 137
  (Polychromatic418967fa.accept_17_11_7_1_1_7023 11 75 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 75 137 (accept_3_2 10 75 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  75 137 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 75 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 75 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 75 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 137 (accept_3_2 7 75 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 75 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 75 137
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 75 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 75 137 (accept_3_2 4 75 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 75
  137 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 75 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 75 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 75 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 137 (accept_3_2 1 75 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 75 137))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 74 137
  (Eq.refl Bool.true) (allA_succ_of_accept 63 74 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 74 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 74 137
  (Polychromatic418967fa.accept_10_2_4_7_1_352 62 74 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 74 137 (accept_3_2 61 74 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  74 137 (Polychromatic418967fa.accept_13_8_9_7_1_530 60 74 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 74 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 74 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 74 137 (accept_3_2 58 74 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 74 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 74 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 74 137
  (Polychromatic418967fa.accept_12_8_2_5_1_844 56 74 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 74 137 (accept_3_2 55 74 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  74 137 (Polychromatic418967fa.accept_13_2_9_7_1_164 54 74 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 74 137 (Polychromatic418967fa.accept_10_3_4_7_1_353 53 74 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 74 137 (accept_3_2 52 74 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 74 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 74 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 74 137
  (Polychromatic418967fa.accept_13_11_9_7_1_2484 50 74 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 74 137 (accept_3_2 49 74 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  74 137 (Polychromatic418967fa.accept_15_3_14_2_1_1888 48 74 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 74 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 74 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 74 137 (accept_3_2 46 74 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 74 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 74 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 74 137
  (Polychromatic418967fa.accept_12_8_2_5_1_844 44 74 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 74 137 (accept_3_2 43 74 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  74 137 (Polychromatic418967fa.accept_10_2_4_7_1_352 42 74 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 74 137 (Polychromatic418967fa.accept_10_1_4_7_1_374 41 74 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 74 137 (accept_3_2 40 74 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 74 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 74 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 74 137
  (Polychromatic418967fa.accept_25_13_24_12_1_7058 38 74 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 74 137 (accept_3_2 37 74 137 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 74 137 (Polychromatic418967fa.accept_11_3_8_5_1_336 36 74 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 74 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 74 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 74 137 (accept_3_2 34 74 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 74 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 33
  74 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 74 137
  (Polychromatic418967fa.accept_10_2_4_7_1_352 32 74 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 74 137 (accept_3_2 31 74 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  74 137 (Polychromatic418967fa.accept_13_4_9_7_1_2402 30 74 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 74 137 (Polychromatic418967fa.accept_13_3_9_7_1_1730 29 74 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 74 137 (accept_3_2 28 74 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 74 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 74 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 74 137
  (Polychromatic418967fa.accept_27_26_20_2_1_7057 26 74 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 74 137 (accept_3_2 25 74 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  74 137 (Polychromatic418967fa.accept_11_2_8_5_1_1219 24 74 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 74 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 74 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 74 137 (accept_3_2 22 74 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 74 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 74 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 74 137
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 74 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 74 137 (accept_3_2 19 74 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  74 137 (Polychromatic418967fa.accept_15_3_14_2_1_1888 18 74 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 74 137 (Polychromatic418967fa.accept_13_4_9_7_1_2402 17 74 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 74 137 (accept_3_2 16 74 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 74 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 74 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 74 137
  (Polychromatic418967fa.accept_11_3_8_5_1_336 14 74 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 74 137 (accept_3_2 13 74 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  74 137 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 74 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 74 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 74 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 74 137 (accept_3_2 10 74 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 74 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 74 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 74 137
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 74 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 74 137 (accept_3_2 7 74 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 74
  137 (Polychromatic418967fa.accept_13_6_9_7_1_2430 6 74 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 74 137 (Polychromatic418967fa.accept_15_5_14_2_1_1876 5 74 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 74 137 (accept_3_2 4 74 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 74 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 74 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 74 137
  (Polychromatic418967fa.accept_10_2_4_7_1_352 2 74 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 74 137 (accept_3_2 1 74 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  137)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 73 137 (Eq.refl Bool.true)
  (allA_of_3_0 65 73 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 66 72 137 (Eq.refl Bool.true)
  (allA_succ_of_accept 65 72 137 (Polychromatic418967fa.accept_10_5_2_7_1_345 65 72 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 72 137 (accept_3_2 64 72 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 72 137 (Polychromatic418967fa.accept_15_3_12_2_1_507 63 72 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 72 137 (Polychromatic418967fa.accept_7_6_2_4_1_291 62
  72 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 137 (accept_3_2 61 72
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 72 137
  (Polychromatic418967fa.accept_16_12_8_9_1_2583 60 72 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 72 137 (Polychromatic418967fa.accept_10_9_2_7_1_1096 59 72 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 72 137 (accept_3_2 58 72 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 72 137 (Polychromatic418967fa.accept_21_15_9_11_1_5417 57 72 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 72 137
  (Polychromatic418967fa.accept_11_1_6_5_1_1732 56 72 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 72 137 (accept_3_2 55 72 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  72 137 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 72 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 72 137 (Polychromatic418967fa.accept_23_7_3_22_1_7056 53 72 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 72 137 (accept_3_2 52 72 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 72 137 (Polychromatic418967fa.accept_14_9_2_11_1_780 51 72 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 72 137
  (Polychromatic418967fa.accept_15_5_12_2_1_2820 50 72 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 72 137 (accept_3_2 49 72 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  72 137 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 72 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 72 137 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 72 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 72 137 (accept_3_2 46 72 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 72 137 (Polychromatic418967fa.accept_10_5_2_7_1_345 45 72 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 72 137
  (Polychromatic418967fa.accept_10_4_2_7_1_373 44 72 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 72 137 (accept_3_2 43 72 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  72 137 (Polychromatic418967fa.accept_17_8_4_1_1_5730 42 72 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 72 137 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 72 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 72 137 (accept_3_2 40 72 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 72 137 (Polychromatic418967fa.accept_10_9_2_7_1_1096 39 72 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 72 137
  (Polychromatic418967fa.accept_25_13_22_12_1_7055 38 72 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 72 137 (accept_3_2 37 72 137 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 72 137 (Polychromatic418967fa.accept_15_6_12_2_1_2803 36 72 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 72 137 (Polychromatic418967fa.accept_10_5_2_7_1_345 35 72 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 72 137 (accept_3_2 34 72 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 72 137 (Polychromatic418967fa.accept_7_5_2_4_1_126 33
  72 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 72 137
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 32 72 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 72 137 (accept_3_2 31 72 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  72 137 (Polychromatic418967fa.accept_19_11_15_4_1_7010 30 72 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 72 137 (Polychromatic418967fa.accept_10_9_2_7_1_1096 29 72 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 72 137 (accept_3_2 28 72 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 72 137 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 72 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 72 137
  (Polychromatic418967fa.accept_7_5_2_4_1_126 26 72 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 72 137 (accept_3_2 25 72 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  72 137 (Polychromatic418967fa.accept_10_4_2_7_1_373 24 72 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 72 137 (Polychromatic418967fa.accept_11_1_6_5_1_1732 23 72 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 72 137 (accept_3_2 22 72 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 72 137 (Polychromatic418967fa.accept_11_10_6_5_1_1239 21 72 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 72 137
  (Polychromatic418967fa.accept_7_6_2_4_1_291 20 72 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 72 137 (accept_3_2 19 72 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  72 137 (Polychromatic418967fa.accept_15_3_12_2_1_507 18 72 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 72 137 (Polychromatic418967fa.accept_16_1_8_9_1_3462 17 72 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 72 137 (accept_3_2 16 72 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 72 137 (Polychromatic418967fa.accept_10_5_2_7_1_345 15 72 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 72 137
  (Polychromatic418967fa.accept_10_4_2_7_1_373 14 72 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 72 137 (accept_3_2 13 72 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  72 137 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 72 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 72 137 (Polychromatic418967fa.accept_19_11_15_4_1_7010 11 72 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 72 137 (accept_3_2 10 72 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 72 137 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 72 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 72 137
  (Polychromatic418967fa.accept_17_8_4_1_1_5730 8 72 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 72 137 (accept_3_2 7 72 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 72
  137 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 72 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 72 137 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 72 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 72 137 (accept_3_2 4 72 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 72 137 (Polychromatic418967fa.accept_15_3_12_2_1_507 3 72 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 72 137 (Polychromatic418967fa.accept_20_2_12_17_1_5547
  2 72 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 137 (accept_3_2 1 72
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72
  137)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 71 137 (Eq.refl Bool.true)
  (allA_succ_of_accept 66 71 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 71 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 137 (Polychromatic418967fa.accept_15_5_11_2_1_1095 65 71
  137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 71 137 (accept_3_2 64 71 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 71 137
  (Polychromatic418967fa.accept_25_13_21_12_1_7054 63 71 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 71 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 137 (accept_3_2 61 71 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 137 (Polychromatic418967fa.accept_9_6_8_2_1_410 60 71 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 137
  (Polychromatic418967fa.accept_7_3_1_4_1_121 59 71 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 137 (accept_3_2 58 71 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 137 (Polychromatic418967fa.accept_9_3_8_2_1_162 57 71 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 137 (Polychromatic418967fa.accept_10_6_1_7_1_342 56 71 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 137 (accept_3_2 55 71 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 71 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 137
  (Polychromatic418967fa.accept_13_1_6_7_1_550 53 71 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 137 (accept_3_2 52 71 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 137 (Polychromatic418967fa.accept_9_6_8_2_1_410 51 71 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 71 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 137 (accept_3_2 49 71 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 137 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 71 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 137
  (Polychromatic418967fa.accept_7_5_1_4_1_122 47 71 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 137 (accept_3_2 46 71 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 137 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 71 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 137 (Polychromatic418967fa.accept_10_4_1_7_1_371 44 71 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 137 (accept_3_2 43 71 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 71 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 137
  (Polychromatic418967fa.accept_9_5_8_2_1_409 41 71 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 137 (accept_3_2 40 71 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 137 (Polychromatic418967fa.accept_9_3_8_2_1_162 39 71 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 71 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 137 (accept_3_2 37 71 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 137 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 71 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 137
  (Polychromatic418967fa.accept_13_9_6_7_1_551 35 71 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 137 (accept_3_2 34 71 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 137 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 71 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 137 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 71 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 137 (accept_3_2 31 71 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 71 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 137
  (Polychromatic418967fa.accept_16_13_7_9_1_2606 29 71 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 137 (accept_3_2 28 71 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 137 (Polychromatic418967fa.accept_13_1_6_7_1_550 27 71 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 71 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 137 (accept_3_2 25 71 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 137 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 71 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 137
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 71 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 137 (accept_3_2 22 71 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 137 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 71 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 137 (Polychromatic418967fa.accept_15_5_11_2_1_1095 20 71 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 137 (accept_3_2 19 71 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 71 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 137
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 71 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 137 (accept_3_2 16 71 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 137 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 71 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 71 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 137 (accept_3_2 13 71 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 137 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 71 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 137
  (Polychromatic418967fa.accept_23_11_2_22_1_7053 11 71 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 137 (accept_3_2 10 71 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 137 (Polychromatic418967fa.accept_13_9_6_7_1_551 9 71 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 137 (Polychromatic418967fa.accept_16_8_7_9_1_7052 8 71 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 137 (accept_3_2 7 71 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 71 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 137
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 71 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 137 (accept_3_2 4 71 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  137 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 71 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 71 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 137 (accept_3_2 1 71 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 137))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 70 137
  (Eq.refl Bool.true) (allA_of_3_0 68 70 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 69 137
  (allA_succ_of_accept 68 69 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 69 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 69 137 (accept_3_2 67 69 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 69 137 (Polychromatic418967fa.accept_7_3_6_4_1_30 66 69 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 69 137 (Polychromatic418967fa.accept_7_2_6_4_1_29 65
  69 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 137 (accept_3_2 64 69
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 137
  (Polychromatic418967fa.accept_11_8_3_5_1_355 63 69 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 69 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 69 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 137 (accept_3_2 61 69 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 69 137 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 69 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 69 137 (Polychromatic418967fa.accept_7_3_6_4_1_30 59
  69 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 137 (accept_3_2 58 69
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 137
  (Polychromatic418967fa.accept_9_3_6_2_1_160 57 69 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 69 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 69 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 69 137 (accept_3_2 55 69 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 69 137 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 69 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 69 137 (Polychromatic418967fa.accept_9_8_6_2_1_744 53
  69 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 137 (accept_3_2 52 69
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 137 (Polychromatic418967fa.accept_7_2_6_4_1_29
  51 69 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 69 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 69 137 (accept_3_2 49 69 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  69 137 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 69 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 69 137 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 69 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 137 (accept_3_2 46 69 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 137 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 69 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 69 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 69 137 (accept_3_2 43 69 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  69 137 (Polychromatic418967fa.accept_10_2_9_7_1_720 42 69 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 69 137 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 69 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 137 (accept_3_2 40 69 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 137 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 69 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 69 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 137 (accept_3_2 37 69 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  69 137 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 69 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 69 137 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 69 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 137 (accept_3_2 34 69 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 137 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 69 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 69 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 137 (accept_3_2 31 69 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  69 137 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 69 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 69 137 (Polychromatic418967fa.accept_13_3_4_7_1_1711 29 69 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 137 (accept_3_2 28 69 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 137 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 69 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 69 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 69 137 (accept_3_2 25 69 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  69 137 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 69 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 69 137 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 69 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 137 (accept_3_2 22 69 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 137 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 69 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 69 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 137 (accept_3_2 19 69 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  69 137 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 69 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 69 137 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 69 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 137 (accept_3_2 16 69 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 137 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 69 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 69 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 137 (accept_3_2 13 69 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  69 137 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 69 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 69 137 (Polychromatic418967fa.accept_13_11_4_7_1_2419 11 69 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 137 (accept_3_2 10 69 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 137 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 69 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 69 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 137 (accept_3_2 7 69 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69
  137 (Polychromatic418967fa.accept_13_6_4_7_1_2464 6 69 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 69 137 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 69 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 137 (accept_3_2 4 69 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 137 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 69 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 69 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 69 137 (accept_3_2 1 69 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  137))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 137 (allA_succ_of_accept 67 68
  137 (accept_3_2 67 68 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 68 137
  (Polychromatic418967fa.accept_9_3_5_2_1_28 66 68 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 68 137 (Polychromatic418967fa.accept_7_2_5_4_1_115 65 68 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 68 137 (accept_3_2 64 68 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 68 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 68 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 68 137 (Polychromatic418967fa.accept_7_6_5_4_1_297 62
  68 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 68 137 (accept_3_2 61 68
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 68 137
  (Polychromatic418967fa.accept_9_6_5_2_1_421 60 68 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 68 137 (Polychromatic418967fa.accept_10_9_8_7_1_714 59 68 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 68 137 (accept_3_2 58 68 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 68 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 68 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 68 137 (Polychromatic418967fa.accept_13_4_3_7_1_2515
  56 68 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 68 137 (accept_3_2 55
  68 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 68 137
  (Polychromatic418967fa.accept_15_9_8_2_1_1109 54 68 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 68 137 (Polychromatic418967fa.accept_8_5_4_1_1_111 53 68 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 68 137 (accept_3_2 52 68 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 68 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 68 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 68 137 (Polychromatic418967fa.accept_7_1_5_4_1_134 50
  68 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 68 137 (accept_3_2 49 68
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 68 137
  (Polychromatic418967fa.accept_7_6_5_4_1_297 48 68 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 68 137 (Polychromatic418967fa.accept_13_8_3_7_1_2455 47 68 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 68 137 (accept_3_2 46 68 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 68 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 68 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 68 137 (Polychromatic418967fa.accept_7_2_5_4_1_115 44
  68 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 68 137 (accept_3_2 43 68
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 68 137
  (Polychromatic418967fa.accept_9_6_5_2_1_421 42 68 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 68 137 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 68 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 68 137 (accept_3_2 40 68 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 68 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 68 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 68 137 (Polychromatic418967fa.accept_12_2_8_5_1_408
  38 68 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 68 137 (accept_3_2 37
  68 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 68 137
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 68 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 68 137 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 68 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 68 137 (accept_3_2 34 68 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 68 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 68 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 137 (Polychromatic418967fa.accept_22_10_2_5_1_7051
  32 68 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 68 137 (accept_3_2 31
  68 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 68 137
  (Polychromatic418967fa.accept_7_2_5_4_1_115 30 68 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 68 137 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 68 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 68 137 (accept_3_2 28 68 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 68 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 68 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 68 137 (Polychromatic418967fa.accept_9_8_5_2_1_422 26
  68 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 68 137 (accept_3_2 25 68
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 68 137
  (Polychromatic418967fa.accept_9_6_5_2_1_421 24 68 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 68 137 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 68 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 68 137 (accept_3_2 22 68 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 68 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 68 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 68 137 (Polychromatic418967fa.accept_7_6_5_4_1_297 20
  68 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 68 137 (accept_3_2 19 68
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 68 137
  (Polychromatic418967fa.accept_19_18_11_4_1_7014 18 68 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 68 137 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 68 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 68 137 (accept_3_2 16 68 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 68 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 68 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 68 137 (Polychromatic418967fa.accept_12_2_8_5_1_408
  14 68 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 68 137 (accept_3_2 13
  68 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 68 137
  (Polychromatic418967fa.accept_9_3_5_2_1_28 12 68 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 68 137 (Polychromatic418967fa.accept_13_11_3_7_1_2513 11 68 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 68 137 (accept_3_2 10 68 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 68 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 68 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 68 137 (Polychromatic418967fa.accept_7_1_5_4_1_134 8
  68 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 68 137 (accept_3_2 7 68 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 68 137 (Polychromatic418967fa.accept_7_6_5_4_1_297 6
  68 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 68 137
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 68 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 68 137 (accept_3_2 4 68 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 68
  137 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 68 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 68 137 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 68 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 137 (accept_3_2 1 68 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 68 137)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 137
  (allA_of_3_0 67 67 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 66 137 (allA_succ_of_accept 65 66 137
  (Polychromatic418967fa.accept_16_1_2_9_1_1607 65 66 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 66 137 (accept_3_2 64 66 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  66 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 66 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 66 137 (Polychromatic418967fa.accept_7_6_3_4_1_294 62 66 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 66 137 (accept_3_2 61 66 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 66 137 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 66 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 66 137
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 66 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 66 137 (accept_3_2 58 66 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  66 137 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 66 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 66 137 (Polychromatic418967fa.accept_15_11_6_2_1_1106 56 66 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 66 137 (accept_3_2 55 66 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 66 137 (Polychromatic418967fa.accept_16_6_2_9_1_5897 54 66 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 66 137
  (Polychromatic418967fa.accept_9_8_3_2_1_417 53 66 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 66 137 (accept_3_2 52 66 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  66 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 66 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 66 137 (Polychromatic418967fa.accept_7_1_3_4_1_128 50 66 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 137 (accept_3_2 49 66 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 66 137 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 66 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 66 137
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 66 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 66 137 (accept_3_2 46 66 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  66 137 (Polychromatic418967fa.accept_13_6_1_7_1_1690 45 66 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 66 137 (Polychromatic418967fa.accept_9_8_3_2_1_417 44 66 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 66 137 (accept_3_2 43 66 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 66 137 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 66 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 66 137
  (Polychromatic418967fa.accept_7_6_3_4_1_294 41 66 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 66 137 (accept_3_2 40 66 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  66 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 66 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 66 137 (Polychromatic418967fa.accept_15_8_6_2_1_1128 38 66 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 66 137 (accept_3_2 37 66 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 66 137 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 66 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 66 137
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 66 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 66 137 (accept_3_2 34 66 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  66 137 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 66 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 66 137 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 66 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 137 (accept_3_2 31 66 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 66 137 (Polychromatic418967fa.accept_24_6_18_17_1_7050 30 66 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 66 137
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 66 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 66 137 (accept_3_2 28 66 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  66 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 66 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 66 137 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 66 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 137 (accept_3_2 25 66 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 66 137 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 66 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 66 137
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 66 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 66 137 (accept_3_2 22 66 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  66 137 (Polychromatic418967fa.accept_10_1_6_7_1_710 21 66 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 66 137 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 66 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 137 (accept_3_2 19 66 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 66 137 (Polychromatic418967fa.accept_21_18_3_11_1_7049 18 66 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 66 137
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 66 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 66 137 (accept_3_2 16 66 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  66 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 66 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 66 137 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 66 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 137 (accept_3_2 13 66 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 66 137 (Polychromatic418967fa.accept_15_12_6_2_1_2760 12 66 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 66 137
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 66 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 66 137 (accept_3_2 10 66 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  66 137 (Polychromatic418967fa.accept_17_9_15_1_1_7048 9 66 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 66 137 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 66 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 137 (accept_3_2 7 66 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 66 137 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 66 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 66 137
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 66 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 66 137 (accept_3_2 4 66 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 66
  137 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 66 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 66 137 (Polychromatic418967fa.accept_19_2_9_4_1_2951 2 66 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 137 (accept_3_2 1 66 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 66 137)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 137
  (allA_succ_of_accept 64 65 137 (accept_3_2 64 65 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  65 137 (Polychromatic418967fa.accept_10_3_5_7_1_330 63 65 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 65 137 (Polychromatic418967fa.accept_7_6_2_4_1_291 62 65 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 137 (accept_3_2 61 65 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 65 137 (Polychromatic418967fa.accept_19_3_8_4_1_5592 60 65 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 137
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 59 65 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 65 137 (accept_3_2 58 65 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  65 137 (Polychromatic418967fa.accept_15_12_5_2_1_2786 57 65 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 65 137 (Polychromatic418967fa.accept_15_11_5_2_1_520 56 65 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 137 (accept_3_2 55 65 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 65 137 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 65 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 137
  (Polychromatic418967fa.accept_10_3_5_7_1_330 53 65 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 65 137 (accept_3_2 52 65 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  65 137 (Polychromatic418967fa.accept_19_13_8_4_1_7047 51 65 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 65 137 (Polychromatic418967fa.accept_11_6_10_5_1_341 50 65 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 137 (accept_3_2 49 65 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 137 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 65 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 137
  (Polychromatic418967fa.accept_7_5_2_4_1_126 47 65 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 65 137 (accept_3_2 46 65 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  65 137 (Polychromatic418967fa.accept_16_13_1_9_1_2597 45 65 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 65 137 (Polychromatic418967fa.accept_14_2_9_11_1_3054 44 65 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 137 (accept_3_2 43 65 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 137 (Polychromatic418967fa.accept_10_2_5_7_1_1124 42 65 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 137
  (Polychromatic418967fa.accept_7_6_2_4_1_291 41 65 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 65 137 (accept_3_2 40 65 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  65 137 (Polychromatic418967fa.accept_11_6_10_5_1_341 39 65 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 65 137 (Polychromatic418967fa.accept_10_8_5_7_1_358 38 65 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 137 (accept_3_2 37 65 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 137 (Polychromatic418967fa.accept_19_17_8_4_1_4212 36 65 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 137
  (Polychromatic418967fa.accept_20_15_5_17_1_5495 35 65 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 65 137 (accept_3_2 34 65 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  65 137 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 65 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 137 (Polychromatic418967fa.accept_10_2_5_7_1_1124 32 65 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 137 (accept_3_2 31 65 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 65 137 (Polychromatic418967fa.accept_14_2_9_11_1_3054 30 65 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 137
  (Polychromatic418967fa.accept_15_14_5_2_1_4761 29 65 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 137 (accept_3_2 28 65 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  65 137 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 65 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 65 137 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 65 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 137 (accept_3_2 25 65 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 137 (Polychromatic418967fa.accept_16_8_1_9_1_847 24 65 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 137
  (Polychromatic418967fa.accept_10_3_5_7_1_330 23 65 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 137 (accept_3_2 22 65 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 137 (Polychromatic418967fa.accept_16_5_1_9_1_4621 21 65 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 137 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 65 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 137 (accept_3_2 19 65 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 137 (Polychromatic418967fa.accept_10_8_5_7_1_358 18 65 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 137
  (Polychromatic418967fa.accept_11_6_10_5_1_341 17 65 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 137 (accept_3_2 16 65 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 137 (Polychromatic418967fa.accept_11_4_10_5_1_1202 15 65 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 137 (Polychromatic418967fa.accept_15_14_5_2_1_4761 14 65 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 137 (accept_3_2 13 65 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 137 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 65 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 137
  (Polychromatic418967fa.accept_15_11_5_2_1_520 11 65 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 137 (accept_3_2 10 65 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 137 (Polychromatic418967fa.accept_19_9_8_4_1_7046 9 65 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 137 (Polychromatic418967fa.accept_10_8_5_7_1_358 8 65 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 137 (accept_3_2 7 65 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 137 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 65 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 137
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 65 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 137 (accept_3_2 4 65 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  137 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 65 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 137 (Polychromatic418967fa.accept_10_2_5_7_1_1124 2 65 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 137 (accept_3_2 1 65 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 137))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 137
  (allA_of_3_0 64 64 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 63 137 (allA_succ_of_accept 62 63 137
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 63 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 137 (accept_3_2 61 63 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  63 137 (Polychromatic418967fa.accept_14_4_7_11_1_790 60 63 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 63 137 (Polychromatic418967fa.accept_14_3_7_11_1_765 59 63 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 137 (accept_3_2 58 63 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 137 (Polychromatic418967fa.accept_11_2_8_5_1_1219 57 63 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 63 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 63 137 (accept_3_2 55 63 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  63 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 63 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 63 137 (Polychromatic418967fa.accept_13_1_11_7_1_1704 53 63 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 137 (accept_3_2 52 63 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 137 (Polychromatic418967fa.accept_13_12_11_7_1_2491 51 63
  137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 137
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 63 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 137 (accept_3_2 49 63 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  63 137 (Polychromatic418967fa.accept_13_9_11_7_1_1077 48 63 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 63 137 (Polychromatic418967fa.accept_11_3_8_5_1_336 47 63 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 137 (accept_3_2 46 63 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 137 (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 63 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 63 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 137 (accept_3_2 43 63 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  63 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 63 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 63 137 (Polychromatic418967fa.accept_19_3_6_4_1_7045 41 63 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 137 (accept_3_2 40 63 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 137 (Polychromatic418967fa.accept_22_17_19_5_1_7044 39 63 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 137
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 63 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 137 (accept_3_2 37 63 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  63 137 (Polychromatic418967fa.accept_10_6_3_7_1_2197 36 63 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 63 137 (Polychromatic418967fa.accept_10_5_3_7_1_1108 35 63 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 137 (accept_3_2 34 63 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 137 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 63 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 63 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 137 (accept_3_2 31 63 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  63 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 63 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 63 137 (Polychromatic418967fa.accept_13_3_11_7_1_2488 29 63 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 137 (accept_3_2 28 63 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 137 (Polychromatic418967fa.accept_13_1_11_7_1_1704 27 63
  137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 137
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 63 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 137 (accept_3_2 25 63 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  63 137 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 63 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 63 137 (Polychromatic418967fa.accept_17_6_12_1_1_7043 23 63 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 137 (accept_3_2 22 63 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 137 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 63 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 63 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 137 (accept_3_2 19 63 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  63 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 63 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 63 137 (Polychromatic418967fa.accept_13_4_11_7_1_558 17 63 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 137 (accept_3_2 16 63 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 137 (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 63 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 137
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 63 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 137 (accept_3_2 13 63 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  63 137 (Polychromatic418967fa.accept_13_12_11_7_1_2491 12 63 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 63 137 (Polychromatic418967fa.accept_27_11_9_2_1_3160 11 63 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 137 (accept_3_2 10 63 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 137 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 63 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 63 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 137 (accept_3_2 7 63 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63
  137 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 63 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 137 (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 63 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 137 (accept_3_2 4 63 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 63 137 (Polychromatic418967fa.accept_11_3_8_5_1_336 3 63 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 63
  137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 137 (accept_3_2 1 63 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  137))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 137 (allA_succ_of_accept 61 62 137
  (accept_3_2 61 62 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 62 137
  (Polychromatic418967fa.accept_9_6_8_2_1_410 60 62 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 62 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 62 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 62 137 (accept_3_2 58 62 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 62 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 62 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 62 137 (Polychromatic418967fa.accept_12_8_2_5_1_844
  56 62 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 62 137 (accept_3_2 55
  62 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 62 137
  (Polychromatic418967fa.accept_7_5_6_4_1_117 54 62 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 62 137 (Polychromatic418967fa.accept_11_9_7_5_1_749 53 62 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 62 137 (accept_3_2 52 62 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 62 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 62 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 62 137 (Polychromatic418967fa.accept_9_5_8_2_1_409 50
  62 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 62 137 (accept_3_2 49 62
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 62 137
  (Polychromatic418967fa.accept_9_3_8_2_1_162 48 62 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 62 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 62 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 62 137 (accept_3_2 46 62 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 62 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 62 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 62 137 (Polychromatic418967fa.accept_7_2_6_4_1_29 44
  62 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 62 137 (accept_3_2 43 62
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 62 137
  (Polychromatic418967fa.accept_9_6_8_2_1_410 42 62 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 62 137 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 62 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 62 137 (accept_3_2 40 62 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 62 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 62 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 62 137 (Polychromatic418967fa.accept_7_3_6_4_1_30 38
  62 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 62 137 (accept_3_2 37 62
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 62 137
  (Polychromatic418967fa.accept_16_4_14_9_1_4657 36 62 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 62 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 62 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 62 137 (accept_3_2 34 62 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 62 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 62 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 62 137 (Polychromatic418967fa.accept_9_5_8_2_1_409 32
  62 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 62 137 (accept_3_2 31 62
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 62 137 (Polychromatic418967fa.accept_7_2_6_4_1_29
  30 62 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 62 137
  (Polychromatic418967fa.accept_10_9_2_7_1_1096 29 62 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 62 137 (accept_3_2 28 62 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  62 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 62 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 62 137 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 62 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 62 137 (accept_3_2 25 62 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 62 137 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 62 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 62 137
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 62 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 62 137 (accept_3_2 22 62 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  62 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 62 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 62 137 (Polychromatic418967fa.accept_11_9_7_5_1_749 20 62 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 62 137 (accept_3_2 19 62 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 62 137 (Polychromatic418967fa.accept_19_18_5_4_1_7042 18 62 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 62 137
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 62 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 62 137 (accept_3_2 16 62 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  62 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 62 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 62 137 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 62 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 62 137 (accept_3_2 13 62 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 62 137 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 62 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 62 137
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 62 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 62 137 (accept_3_2 10 62 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  62 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 62 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 62 137 (Polychromatic418967fa.accept_12_8_2_5_1_844 8 62 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 62 137 (accept_3_2 7 62 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 62 137 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 62 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 62 137
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 62 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 62 137 (accept_3_2 4 62 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 62
  137 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 62 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 62 137 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 62 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 137 (accept_3_2 1 62 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 62 137)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 137
  (allA_of_3_0 61 61 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 60 137 (allA_succ_of_accept 59 60 137
  (Polychromatic418967fa.accept_9_5_6_2_1_161 59 60 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 60 137 (accept_3_2 58 60 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  60 137 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 60 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 60 137 (Polychromatic418967fa.accept_16_8_12_9_1_2569 56 60 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 60 137 (accept_3_2 55 60 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 60 137 (Polychromatic418967fa.accept_13_2_8_7_1_2424 54 60 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 60 137
  (Polychromatic418967fa.accept_8_5_4_1_1_111 53 60 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 60 137 (accept_3_2 52 60 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  60 137 (Polychromatic418967fa.accept_13_12_8_7_1_2526 51 60 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 60 137 (Polychromatic418967fa.accept_9_5_6_2_1_161 50 60 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 60 137 (accept_3_2 49 60 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 60 137 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 60 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 60 137
  (Polychromatic418967fa.accept_21_5_18_11_1_7041 47 60 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 60 137 (accept_3_2 46 60 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  60 137 (Polychromatic418967fa.accept_8_5_4_1_1_111 45 60 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 60 137 (Polychromatic418967fa.accept_9_8_6_2_1_744 44 60 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 137 (accept_3_2 43 60 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 60 137 (Polychromatic418967fa.accept_13_3_8_7_1_4135 42 60 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 60 137
  (Polychromatic418967fa.accept_9_5_6_2_1_161 41 60 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 60 137 (accept_3_2 40 60 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  60 137 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 60 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 60 137 (Polychromatic418967fa.accept_13_12_8_7_1_2526 38 60 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 137 (accept_3_2 37 60 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 60 137 (Polychromatic418967fa.accept_13_10_8_7_1_1074 36 60
  137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 60 137
  (Polychromatic418967fa.accept_9_8_6_2_1_744 35 60 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 60 137 (accept_3_2 34 60 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  60 137 (Polychromatic418967fa.accept_18_15_6_11_1_5651 33 60 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 60 137 (Polychromatic418967fa.accept_9_5_6_2_1_161 32 60 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 137 (accept_3_2 31 60 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 60 137 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 60 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 60 137
  (Polychromatic418967fa.accept_8_5_4_1_1_111 29 60 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 60 137 (accept_3_2 28 60 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  60 137 (Polychromatic418967fa.accept_13_1_8_7_1_1088 27 60 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 60 137 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 60 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 60 137 (accept_3_2 25 60 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 60 137 (Polychromatic418967fa.accept_16_8_12_9_1_2569 24 60 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 60 137
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 60 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 60 137 (accept_3_2 22 60 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  60 137 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 60 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 60 137 (Polychromatic418967fa.accept_16_4_12_9_1_2567 20 60 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 137 (accept_3_2 19 60 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 60 137 (Polychromatic418967fa.accept_16_2_12_9_1_2568 18 60
  137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 60 137
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 60 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 60 137 (accept_3_2 16 60 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  60 137 (Polychromatic418967fa.accept_13_2_8_7_1_2424 15 60 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 60 137 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 60 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 137 (accept_3_2 13 60 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 60 137 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 60 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 60 137
  (Polychromatic418967fa.accept_19_11_3_4_1_4242 11 60 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 60 137 (accept_3_2 10 60 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  60 137 (Polychromatic418967fa.accept_13_9_8_7_1_1073 9 60 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 60 137 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 60 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 137 (accept_3_2 7 60 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 60 137 (Polychromatic418967fa.accept_19_6_3_4_1_7040 6 60 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 60 137
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 60 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 60 137 (accept_3_2 4 60 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 60
  137 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 60 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 60 137 (Polychromatic418967fa.accept_13_2_8_7_1_2424 2 60 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 137 (accept_3_2 1 60 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 60 137)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 137
  (allA_succ_of_accept 58 59 137 (accept_3_2 58 59 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  59 137 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 59 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 59 137 (Polychromatic418967fa.accept_19_18_2_4_1_7039 56 59 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 137 (accept_3_2 55 59 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 59 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 59 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 137
  (Polychromatic418967fa.accept_9_8_5_2_1_422 53 59 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 137 (accept_3_2 52 59 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 137 (Polychromatic418967fa.accept_9_6_5_2_1_421 51 59 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 59 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 137 (accept_3_2 49 59 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 137 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 59 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 137
  (Polychromatic418967fa.accept_19_9_2_4_1_7038 47 59 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 137 (accept_3_2 46 59 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 137 (Polychromatic418967fa.accept_17_11_8_1_1_3362 45 59 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 137 (Polychromatic418967fa.accept_9_8_5_2_1_422 44 59 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 137 (accept_3_2 43 59 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 59 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 137
  (Polychromatic418967fa.accept_7_6_3_4_1_294 41 59 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 137 (accept_3_2 40 59 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 137 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 59 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 59 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 137 (accept_3_2 37 59 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 137 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 59 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 137
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 59 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 137 (accept_3_2 34 59 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 137 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 59 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 137 (Polychromatic418967fa.accept_10_2_9_7_1_720 32 59 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 137 (accept_3_2 31 59 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 59 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 137
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 59 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 137 (accept_3_2 28 59 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 137 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 59 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 59 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 137 (accept_3_2 25 59 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 137 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 59 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 137
  (Polychromatic418967fa.accept_21_2_17_11_1_7037 23 59 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 137 (accept_3_2 22 59 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 137 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 59 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 137 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 59 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 137 (accept_3_2 19 59 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 59 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 137
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 59 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 137 (accept_3_2 16 59 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 137 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 59 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 59 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 137 (accept_3_2 13 59 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 137 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 59 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 137
  (Polychromatic418967fa.accept_17_11_8_1_1_3362 11 59 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 137 (accept_3_2 10 59 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 137 (Polychromatic418967fa.accept_17_9_8_1_1_7036 9 59 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 137 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 59 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 137 (accept_3_2 7 59 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 59 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 137
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 5 59 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 137 (accept_3_2 4 59 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  137 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 59 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 59 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 59 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 137 (accept_3_2 1 59 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 59 137))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 137 (allA_of_3_0
  58 58 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 57 137 (allA_succ_of_accept 56 57 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 57 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 137 (accept_3_2 55 57 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  57 137 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 57 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 57 137 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 57 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 137 (accept_3_2 52 57 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 137 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 57 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 57 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 137 (accept_3_2 49 57 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  57 137 (Polychromatic418967fa.accept_15_3_12_2_1_507 48 57 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 57 137 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 57 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 137 (accept_3_2 46 57 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 137 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 57 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 57 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 137 (accept_3_2 43 57 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  57 137 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 57 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 57 137 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 57 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 137 (accept_3_2 40 57 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 137 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 57 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 57 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 137 (accept_3_2 37 57 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  57 137 (Polychromatic418967fa.accept_15_6_12_2_1_2803 36 57 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 57 137 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 57 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 137 (accept_3_2 34 57 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 137 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 57 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 57 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 137 (accept_3_2 31 57 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  57 137 (Polychromatic418967fa.accept_11_8_2_5_1_1769 30 57 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 57 137 (Polychromatic418967fa.accept_15_14_12_2_1_3804 29 57 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 137 (accept_3_2 28 57 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 137 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 57 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 57 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 137 (accept_3_2 25 57 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  57 137 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 57 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 57 137 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 57 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 137 (accept_3_2 22 57 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 137 (Polychromatic418967fa.accept_15_6_12_2_1_2803 21 57 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 57 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 137 (accept_3_2 19 57 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  57 137 (Polychromatic418967fa.accept_14_4_1_11_1_5026 18 57 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 57 137 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 57 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 137 (accept_3_2 16 57 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 137 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 57 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 57 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 137 (accept_3_2 13 57 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  57 137 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 57 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 57 137 (Polychromatic418967fa.accept_13_11_5_7_1_2420 11 57 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 137 (accept_3_2 10 57 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 137 (Polychromatic418967fa.accept_21_9_15_11_1_7018 9 57 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 57 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 137 (accept_3_2 7 57 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57
  137 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 57 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 137 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 57 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 137 (accept_3_2 4 57 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 137 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 57 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 57
  137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 137 (accept_3_2 1 57 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 137)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 137 (allA_succ_of_accept 55 56 137 (accept_3_2 55 56 137 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 56 137 (Polychromatic418967fa.accept_15_9_11_2_1_1882 54 56 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 56 137 (Polychromatic418967fa.accept_10_3_6_7_1_2188 53 56 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 137 (accept_3_2 52 56 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 56 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 51
  56 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 56 137
  (Polychromatic418967fa.accept_11_6_1_5_1_2388 50 56 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 56 137 (accept_3_2 49 56 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  56 137 (Polychromatic418967fa.accept_13_9_4_7_1_1694 48 56 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 56 137 (Polychromatic418967fa.accept_16_15_8_9_1_2563 47 56 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 137 (accept_3_2 46 56 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 56 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 56 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 137
  (Polychromatic418967fa.accept_16_12_8_9_1_2583 44 56 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 56 137 (accept_3_2 43 56 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  56 137 (Polychromatic418967fa.accept_13_3_4_7_1_1711 42 56 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 56 137 (Polychromatic418967fa.accept_10_1_6_7_1_710 41 56 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 56 137 (accept_3_2 40 56 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 56 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 56 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 137
  (Polychromatic418967fa.accept_12_2_8_5_1_408 38 56 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 56 137 (accept_3_2 37 56 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  56 137 (Polychromatic418967fa.accept_13_10_4_7_1_2465 36 56 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 56 137 (Polychromatic418967fa.accept_13_9_4_7_1_1694 35 56 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 56 137 (accept_3_2 34 56 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 56 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 56 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 56 137
  (Polychromatic418967fa.accept_13_6_4_7_1_2464 32 56 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 56 137 (accept_3_2 31 56 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  56 137 (Polychromatic418967fa.accept_19_11_18_4_1_2957 30 56 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 56 137 (Polychromatic418967fa.accept_13_3_4_7_1_1711 29 56 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 56 137 (accept_3_2 28 56 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 56 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 56 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 137
  (Polychromatic418967fa.accept_12_2_8_5_1_408 26 56 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 56 137 (accept_3_2 25 56 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  56 137 (Polychromatic418967fa.accept_13_11_4_7_1_2419 24 56 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 56 137 (Polychromatic418967fa.accept_10_3_6_7_1_2188 23 56 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 137 (accept_3_2 22 56 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 56 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 56 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 56 137
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 20 56 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 56 137 (accept_3_2 19 56 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  56 137 (Polychromatic418967fa.accept_21_18_14_11_1_7035 18 56 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 56 137 (Polychromatic418967fa.accept_11_6_1_5_1_2388 17 56 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 137 (accept_3_2 16 56 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 56 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 56 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 56 137
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 56 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 56 137 (accept_3_2 13 56 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  56 137 (Polychromatic418967fa.accept_13_12_4_7_1_2520 12 56 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 56 137 (Polychromatic418967fa.accept_10_1_6_7_1_710 11 56 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 137 (accept_3_2 10 56 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 56 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 56 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 137
  (Polychromatic418967fa.accept_19_8_18_4_1_4274 8 56 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 56 137 (accept_3_2 7 56 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 56
  137 (Polychromatic418967fa.accept_11_6_1_5_1_2388 6 56 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 56 137 (Polychromatic418967fa.accept_15_5_11_2_1_1095 5 56 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 137 (accept_3_2 4 56 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 56 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 56 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 137
  (Polychromatic418967fa.accept_12_2_8_5_1_408 2 56 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 56 137 (accept_3_2 1 56 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56
  137)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 55 137 (allA_of_3_0 55 55 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 54 137 (allA_succ_of_accept 53 54 137
  (Polychromatic418967fa.accept_10_3_4_7_1_353 53 54 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 54 137 (accept_3_2 52 54 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  54 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 54 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 54 137 (Polychromatic418967fa.accept_7_1_5_4_1_134 50 54 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 137 (accept_3_2 49 54 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 137 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 54 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 54 137
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 54 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 54 137 (accept_3_2 46 54 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  54 137 (Polychromatic418967fa.accept_16_13_6_9_1_2561 45 54 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 54 137 (Polychromatic418967fa.accept_7_2_5_4_1_115 44 54 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 137 (accept_3_2 43 54 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 137 (Polychromatic418967fa.accept_10_2_4_7_1_352 42 54 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 54 137
  (Polychromatic418967fa.accept_7_6_5_4_1_297 41 54 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 54 137 (accept_3_2 40 54 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  54 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 54 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 54 137 (Polychromatic418967fa.accept_15_8_9_2_1_1897 38 54 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 137 (accept_3_2 37 54 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 54 137 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 54 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 54 137
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 54 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 54 137 (accept_3_2 34 54 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  54 137 (Polychromatic418967fa.accept_10_3_4_7_1_353 33 54 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 54 137 (Polychromatic418967fa.accept_10_2_4_7_1_352 32 54 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 137 (accept_3_2 31 54 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 54 137 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 54 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 54 137
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 54 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 54 137 (accept_3_2 28 54 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  54 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 54 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 54 137 (Polychromatic418967fa.accept_11_4_10_5_1_1202 26 54 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 137 (accept_3_2 25 54 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 54 137 (Polychromatic418967fa.accept_21_3_12_11_1_7034 24 54
  137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 54 137
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 54 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 54 137 (accept_3_2 22 54 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  54 137 (Polychromatic418967fa.accept_10_1_4_7_1_374 21 54 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 54 137 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 54 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 137 (accept_3_2 19 54 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 54 137 (Polychromatic418967fa.accept_13_5_2_7_1_2414 18 54 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 54 137
  (Polychromatic418967fa.accept_11_6_10_5_1_341 17 54 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 54 137 (accept_3_2 16 54 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  54 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 54 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 54 137 (Polychromatic418967fa.accept_21_14_12_11_1_3956 14 54 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 137 (accept_3_2 13 54 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 54 137 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 54 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 54 137
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 54 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 54 137 (accept_3_2 10 54 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  54 137 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 54 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 54 137 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 54 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 137 (accept_3_2 7 54 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 54 137 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 54 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 54 137
  (Polychromatic418967fa.accept_13_5_2_7_1_2414 5 54 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 54 137 (accept_3_2 4 54 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 54
  137 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 54 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 54 137 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 54 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 137 (accept_3_2 1 54 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 54 137)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 137
  (allA_succ_of_accept 52 53 137 (accept_3_2 52 53 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  53 137 (Polychromatic418967fa.accept_9_6_8_2_1_410 51 53 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 53 137 (Polychromatic418967fa.accept_9_5_8_2_1_409 50 53 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 137 (accept_3_2 49 53 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 53 137 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 53 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 137
  (Polychromatic418967fa.accept_13_8_1_7_1_2505 47 53 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 53 137 (accept_3_2 46 53 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  53 137 (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 53 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 53 137 (Polychromatic418967fa.accept_8_4_5_1_1_299 44 53 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 137 (accept_3_2 43 53 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 53 137 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 53 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 137
  (Polychromatic418967fa.accept_9_5_8_2_1_409 41 53 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 137 (accept_3_2 40 53 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 137 (Polychromatic418967fa.accept_9_3_8_2_1_162 39 53 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 137 (Polychromatic418967fa.accept_18_2_17_11_1_3178 38 53 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 137 (accept_3_2 37 53 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 137 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 53 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 137
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 35 53 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 137 (accept_3_2 34 53 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 137 (Polychromatic418967fa.accept_9_6_8_2_1_410 33 53 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 137 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 53 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 137 (accept_3_2 31 53 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 137 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 53 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 137
  (Polychromatic418967fa.accept_11_7_9_5_1_338 29 53 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 137 (accept_3_2 28 53 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 137 (Polychromatic418967fa.accept_16_11_5_9_1_1617 27 53 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 137 (Polychromatic418967fa.accept_10_6_3_7_1_2197 26 53 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 137 (accept_3_2 25 53 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 137 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 53 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 137
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 53 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 137 (accept_3_2 22 53 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 137 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 53 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 137 (Polychromatic418967fa.accept_8_4_5_1_1_299 20 53 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 137 (accept_3_2 19 53 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 137 (Polychromatic418967fa.accept_11_7_9_5_1_338 18 53 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 137
  (Polychromatic418967fa.accept_16_1_5_9_1_1649 17 53 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 137 (accept_3_2 16 53 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 137 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 53 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 137 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 53 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 137 (accept_3_2 13 53 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 137 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 53 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 137
  (Polychromatic418967fa.accept_13_11_1_7_1_1691 11 53 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 137 (accept_3_2 10 53 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 137 (Polychromatic418967fa.accept_15_9_8_2_1_1109 9 53 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 137 (Polychromatic418967fa.accept_13_8_1_7_1_2505 8 53 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 137 (accept_3_2 7 53 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 137 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 53 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 137
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 53 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 137 (accept_3_2 4 53 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  137 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 53 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 137 (Polychromatic418967fa.accept_18_2_17_11_1_3178 2 53 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 137 (accept_3_2 1 53 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 137))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 137 (allA_of_3_0 52 52
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 137 (allA_succ_of_accept 50 51 137
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 51 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 137 (accept_3_2 49 51 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  51 137 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 51 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 51 137 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 51 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 137 (accept_3_2 46 51 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 137 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 51 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 51 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 137 (accept_3_2 43 51 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  51 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 51 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 51 137 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 51 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 137 (accept_3_2 40 51 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 137 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 51 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 137
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 51 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 137 (accept_3_2 37 51 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  51 137 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 51 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 51 137 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 51 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 137 (accept_3_2 34 51 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 137 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 51 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 51 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 137 (accept_3_2 31 51 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  51 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 51 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 51 137 (Polychromatic418967fa.accept_19_10_13_4_1_5583 29 51 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 137 (accept_3_2 28 51 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 137 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 51 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 137
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 51 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 137 (accept_3_2 25 51 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  51 137 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 51 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 51 137 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 51 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 137 (accept_3_2 22 51 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 137 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 51 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 51 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 137 (accept_3_2 19 51 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  51 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 51 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 51 137 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 51 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 137 (accept_3_2 16 51 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 137 (Polychromatic418967fa.accept_19_15_13_4_1_7033 15 51 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 137
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 51 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 137 (accept_3_2 13 51 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  51 137 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 51 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 51 137 (Polychromatic418967fa.accept_13_11_12_7_1_2443 11 51 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 137 (accept_3_2 10 51 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 137 (Polychromatic418967fa.accept_11_9_7_5_1_749 9 51 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 51 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 137 (accept_3_2 7 51 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51
  137 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 51 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 137 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 51 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 137 (accept_3_2 4 51 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 51 137 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 51 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 51
  137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 137 (accept_3_2 1 51 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 137)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 137 (allA_succ_of_accept 49 50 137 (accept_3_2 49 50 137 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 50 137 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 50 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 50 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 50 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 137 (accept_3_2 46 50 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 50 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 45
  50 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 50 137
  (Polychromatic418967fa.accept_9_8_5_2_1_422 44 50 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 50 137 (accept_3_2 43 50 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  50 137 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 50 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 50 137 (Polychromatic418967fa.accept_15_11_5_2_1_520 41 50 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 50 137 (accept_3_2 40 50 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 50 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 50 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 137
  (Polychromatic418967fa.accept_7_3_1_4_1_121 38 50 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 50 137 (accept_3_2 37 50 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  50 137 (Polychromatic418967fa.accept_17_2_16_1_1_2260 36 50 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 50 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 50 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 50 137 (accept_3_2 34 50 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 50 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 50 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 50 137
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 32 50 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 50 137 (accept_3_2 31 50 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  50 137 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 50 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 50 137 (Polychromatic418967fa.accept_13_3_11_7_1_2488 29 50 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 137 (accept_3_2 28 50 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 50 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 50 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 137
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 50 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 50 137 (accept_3_2 25 50 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  50 137 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 50 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 50 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 50 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 137 (accept_3_2 22 50 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 50 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 50 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 50 137
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 50 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 50 137 (accept_3_2 19 50 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  50 137 (Polychromatic418967fa.accept_13_5_11_7_1_559 18 50 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 50 137 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 50 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 137 (accept_3_2 16 50 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 50 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 50 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 50 137
  (Polychromatic418967fa.accept_13_1_11_7_1_1704 14 50 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 50 137 (accept_3_2 13 50 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  50 137 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 50 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 50 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 50 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 50 137 (accept_3_2 10 50 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 50 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 50 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 137
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 50 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 50 137 (accept_3_2 7 50 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50
  137 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 50 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 50 137 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 50 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 50 137 (accept_3_2 4 50 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 50 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 50 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 137 (Polychromatic418967fa.accept_17_2_16_1_1_2260
  2 50 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 50 137 (accept_3_2 1 50
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 137))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 49 137 (allA_of_3_0 49 49 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 48 137
  (allA_succ_of_accept 47 48 137 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 48 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 48 137 (accept_3_2 46 48 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 48 137 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 48 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 48 137 (Polychromatic418967fa.accept_7_2_6_4_1_29 44
  48 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 137 (accept_3_2 43 48
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 48 137
  (Polychromatic418967fa.accept_9_6_3_2_1_431 42 48 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 48 137 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 48 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 48 137 (accept_3_2 40 48 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 48 137 (Polychromatic418967fa.accept_10_9_8_7_1_714 39 48 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 48 137 (Polychromatic418967fa.accept_7_3_6_4_1_30 38
  48 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 137 (accept_3_2 37 48
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 137
  (Polychromatic418967fa.accept_19_17_10_4_1_7032 36 48 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 48 137 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 48 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 48 137 (accept_3_2 34 48 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 48 137 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 48 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 48 137 (Polychromatic418967fa.accept_9_5_3_2_1_171 32
  48 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 137 (accept_3_2 31 48
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 137 (Polychromatic418967fa.accept_7_2_6_4_1_29
  30 48 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 48 137
  (Polychromatic418967fa.accept_10_9_8_7_1_714 29 48 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 48 137 (accept_3_2 28 48 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  48 137 (Polychromatic418967fa.accept_15_12_3_2_1_2756 27 48 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 48 137 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 48 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 137 (accept_3_2 25 48 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 137 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 48 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 48 137
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 48 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 48 137 (accept_3_2 22 48 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  48 137 (Polychromatic418967fa.accept_11_10_4_5_1_359 21 48 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 48 137 (Polychromatic418967fa.accept_15_5_3_2_1_5930 20 48 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 137 (accept_3_2 19 48 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 48 137 (Polychromatic418967fa.accept_21_18_6_11_1_7031 18 48 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 48 137
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 48 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 48 137 (accept_3_2 16 48 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  48 137 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 48 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 48 137 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 48 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 137 (accept_3_2 13 48 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 48 137 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 48 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 48 137
  (Polychromatic418967fa.accept_13_11_9_7_1_2484 11 48 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 48 137 (accept_3_2 10 48 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  48 137 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 48 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 48 137 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 48 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 137 (accept_3_2 7 48 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 137 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 48 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 48 137
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 48 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 48 137 (accept_3_2 4 48 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 48
  137 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 48 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 48 137 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 48 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 137 (accept_3_2 1 48 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 48 137)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 137 (allA_succ_of_accept 46
  47 137 (accept_3_2 46 47 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 137
  (Polychromatic418967fa.accept_22_1_3_5_1_375 45 47 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 137 (Polychromatic418967fa.accept_7_2_5_4_1_115 44 47 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 137 (accept_3_2 43 47 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 47 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 137 (Polychromatic418967fa.accept_7_6_5_4_1_297 41
  47 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 137 (accept_3_2 40 47
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 137
  (Polychromatic418967fa.accept_20_19_7_17_1_7030 39 47 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 47 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 47 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 137 (accept_3_2 37 47 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 47 137 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 47 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 137 (Polychromatic418967fa.accept_13_9_8_7_1_1073
  35 47 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 137 (accept_3_2 34
  47 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 137
  (Polychromatic418967fa.accept_19_14_9_4_1_7029 33 47 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 47 137 (Polychromatic418967fa.accept_19_13_9_4_1_4309 32 47 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 137 (accept_3_2 31 47 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 47 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 47 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 137 (Polychromatic418967fa.accept_7_1_5_4_1_134 29
  47 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 137 (accept_3_2 28 47
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 47 137
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 47 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 47 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 47 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 137 (accept_3_2 25 47 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 47 137 (Polychromatic418967fa.accept_16_8_15_9_1_4676 24 47 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 137
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 47 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 137 (accept_3_2 22 47 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 137 (Polychromatic418967fa.accept_19_2_9_4_1_2951 21 47 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 137 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 47 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 137 (accept_3_2 19 47 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 47 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 137
  (Polychromatic418967fa.accept_21_17_5_11_1_7028 17 47 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 137 (accept_3_2 16 47 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 137 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 47 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 47 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 137 (accept_3_2 13 47 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 137 (Polychromatic418967fa.accept_13_12_8_7_1_2526 12 47 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 137
  (Polychromatic418967fa.accept_24_11_23_17_1_7012 11 47 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 47 137 (accept_3_2 10 47 137 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 47 137 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 47 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 47 137 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 47 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 137 (accept_3_2 7 47 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 47
  137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 137
  (Polychromatic418967fa.accept_19_5_9_4_1_232 5 47 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 137 (accept_3_2 4 47 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  137 (Polychromatic418967fa.accept_13_3_8_7_1_4135 3 47 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 47 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 47 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 137 (accept_3_2 1 47 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 47 137))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 137 (allA_of_3_0 46
  46 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 45 137 (allA_succ_of_accept 44 45 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 45 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 137 (accept_3_2 43 45 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  45 137 (Polychromatic418967fa.accept_10_2_5_7_1_1124 42 45 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 45 137 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 45 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 137 (accept_3_2 40 45 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 137 (Polychromatic418967fa.accept_11_6_1_5_1_2388 39 45 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 45 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 137 (accept_3_2 37 45 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  45 137 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 45 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 45 137 (Polychromatic418967fa.accept_13_9_6_7_1_551 35 45 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 137 (accept_3_2 34 45 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 137 (Polychromatic418967fa.accept_10_3_5_7_1_330 33 45 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 45 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 137 (accept_3_2 31 45 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  45 137 (Polychromatic418967fa.accept_13_4_6_7_1_2471 30 45 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 45 137 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 45 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 137 (accept_3_2 28 45 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 137 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 45 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 45 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 137 (accept_3_2 25 45 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  45 137 (Polychromatic418967fa.accept_17_7_11_1_1_4503 24 45 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 45 137 (Polychromatic418967fa.accept_10_3_5_7_1_330 23 45 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 137 (accept_3_2 22 45 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 137 (Polychromatic418967fa.accept_14_7_3_11_1_2199 21 45 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 45 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 45 137 (accept_3_2 19 45 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  45 137 (Polychromatic418967fa.accept_10_8_5_7_1_358 18 45 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 45 137 (Polychromatic418967fa.accept_11_6_1_5_1_2388 17 45 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 137 (accept_3_2 16 45 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 137 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 45 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 45 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 137 (accept_3_2 13 45 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  45 137 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 45 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 45 137 (Polychromatic418967fa.accept_19_11_7_4_1_4308 11 45 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 137 (accept_3_2 10 45 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 137 (Polychromatic418967fa.accept_13_9_6_7_1_551 9 45 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 45 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 137 (accept_3_2 7 45 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45
  137 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 45 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 137 (Polychromatic418967fa.accept_16_5_13_9_1_2594 5 45 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 137 (accept_3_2 4 45 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 45 137 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 45 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 45
  137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 137 (accept_3_2 1 45 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 137))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  137 (allA_succ_of_accept 43 44 137 (accept_3_2 43 44 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 44 137 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 44 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 44 137 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 44 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 137 (accept_3_2 40 44 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 44 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 44 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 137
  (Polychromatic418967fa.accept_12_2_8_5_1_408 38 44 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 44 137 (accept_3_2 37 44 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  44 137 (Polychromatic418967fa.accept_16_4_12_9_1_2567 36 44 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 44 137 (Polychromatic418967fa.accept_15_5_14_2_1_1876 35 44 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 137 (accept_3_2 34 44 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 44 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 44 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 44 137
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 44 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 44 137 (accept_3_2 31 44 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  44 137 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 44 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 44 137 (Polychromatic418967fa.accept_8_5_4_1_1_111 29 44 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 44 137 (accept_3_2 28 44 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 44 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 44 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 44 137
  (Polychromatic418967fa.accept_7_5_2_4_1_126 26 44 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 44 137 (accept_3_2 25 44 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  44 137 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 44 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 44 137 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 44 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 44 137 (accept_3_2 22 44 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 44 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 44 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 44 137
  (Polychromatic418967fa.accept_7_6_2_4_1_291 20 44 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 44 137 (accept_3_2 19 44 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  44 137 (Polychromatic418967fa.accept_15_3_14_2_1_1888 18 44 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 44 137 (Polychromatic418967fa.accept_19_17_6_4_1_7027 17 44 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 44 137 (accept_3_2 16 44 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 44 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 44 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 44 137
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 44 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 44 137 (accept_3_2 13 44 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  44 137 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 44 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 44 137 (Polychromatic418967fa.accept_10_1_4_7_1_374 11 44 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 44 137 (accept_3_2 10 44 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 44 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 44 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 44 137
  (Polychromatic418967fa.accept_16_8_12_9_1_2569 8 44 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 44 137 (accept_3_2 7 44 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 44
  137 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 44 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 44 137 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 44 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 44 137 (accept_3_2 4 44 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 44 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 44 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 44 137 (Polychromatic418967fa.accept_10_2_4_7_1_352 2
  44 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 137 (accept_3_2 1 44 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44 137)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43
  137 (allA_of_3_0 43 43 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 137 (allA_succ_of_accept 41 42 137
  (Polychromatic418967fa.accept_9_5_6_2_1_161 41 42 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 42 137 (accept_3_2 40 42 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  42 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 42 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 42 137 (Polychromatic418967fa.accept_17_4_8_1_1_5740 38 42 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 137 (accept_3_2 37 42 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 137 (Polychromatic418967fa.accept_13_10_3_7_1_2517 36 42 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 42 137
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 42 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 42 137 (accept_3_2 34 42 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  42 137 (Polychromatic418967fa.accept_15_3_12_2_1_507 33 42 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 42 137 (Polychromatic418967fa.accept_9_5_6_2_1_161 32 42 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 137 (accept_3_2 31 42 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 42 137 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 42 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 42 137
  (Polychromatic418967fa.accept_10_9_2_7_1_1096 29 42 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 42 137 (accept_3_2 28 42 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  42 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 42 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 42 137 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 42 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 137 (accept_3_2 25 42 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 137 (Polychromatic418967fa.accept_10_4_2_7_1_373 24 42 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 42 137
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 42 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 42 137 (accept_3_2 22 42 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  42 137 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 42 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 42 137 (Polychromatic418967fa.accept_15_5_12_2_1_2820 20 42 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 137 (accept_3_2 19 42 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 42 137 (Polychromatic418967fa.accept_11_7_9_5_1_338 18 42 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 42 137
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 42 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 42 137 (accept_3_2 16 42 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  42 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 42 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 42 137 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 42 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 137 (accept_3_2 13 42 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 137 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 42 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 42 137
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 42 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 42 137 (accept_3_2 10 42 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  42 137 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 42 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 42 137 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 42 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 137 (accept_3_2 7 42 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 42 137 (Polychromatic418967fa.accept_15_6_12_2_1_2803 6 42 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 42 137
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 42 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 42 137 (accept_3_2 4 42 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 42
  137 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 42 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 42 137 (Polychromatic418967fa.accept_23_2_19_22_1_7026 2 42 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 137 (accept_3_2 1 42 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 42 137)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 137 (allA_succ_of_accept 40 41
  137 (accept_3_2 40 41 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 137
  (Polychromatic418967fa.accept_9_3_5_2_1_28 39 41 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 137 (Polychromatic418967fa.accept_7_3_6_4_1_30 38 41 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 137 (accept_3_2 37 41 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 137 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 41 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 137 (Polychromatic418967fa.accept_9_8_5_2_1_422 35
  41 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 137 (accept_3_2 34 41
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 137
  (Polychromatic418967fa.accept_7_5_6_4_1_117 33 41 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 41 137 (Polychromatic418967fa.accept_18_14_5_11_1_5676 32 41 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 137 (accept_3_2 31 41 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 41 137 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 41 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 137
  (Polychromatic418967fa.accept_21_8_20_11_1_7025 29 41 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 137 (accept_3_2 28 41 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 137 (Polychromatic418967fa.accept_17_10_7_1_1_7024 27 41 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 137 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 41 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 137 (accept_3_2 25 41 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 137 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 41 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 137
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 41 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 137 (accept_3_2 22 41 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 137 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 41 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 137 (Polychromatic418967fa.accept_15_5_11_2_1_1095 20 41 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 137 (accept_3_2 19 41 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 137 (Polychromatic418967fa.accept_13_5_2_7_1_2414 18 41 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 137
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 41 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 137 (accept_3_2 16 41 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 137 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 41 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 137 (Polychromatic418967fa.accept_10_4_1_7_1_371 14 41 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 137 (accept_3_2 13 41 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 137 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 41 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 137
  (Polychromatic418967fa.accept_17_11_7_1_1_7023 11 41 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 137 (accept_3_2 10 41 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 137 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 41 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 137 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 41 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 137 (accept_3_2 7 41 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 137 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 41 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 137
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 41 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 137 (accept_3_2 4 41 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  137 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 41 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 137 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 41 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 137 (accept_3_2 1 41 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 137))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 137 (allA_of_3_0 40 40 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 137 (allA_succ_of_accept 38 39 137
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 39 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 137 (accept_3_2 37 39 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 137 (Polychromatic418967fa.accept_19_17_1_4_1_7022 36 39 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 137 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 39 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 137 (accept_3_2 34 39 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 137 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 39 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 39 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 137 (accept_3_2 31 39 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 39 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 137 (Polychromatic418967fa.accept_16_13_7_9_1_2606 29 39 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 137 (accept_3_2 28 39 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 137 (Polychromatic418967fa.accept_20_7_19_17_1_2794 27 39
  137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 137
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 39 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 137 (accept_3_2 25 39 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 137 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 39 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 137 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 39 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 137 (accept_3_2 22 39 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 137 (Polychromatic418967fa.accept_11_10_6_5_1_1239 21 39 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 39 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 137 (accept_3_2 19 39 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 39 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 137 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 39 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 137 (accept_3_2 16 39 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 137 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 39 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 137
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 39 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 137 (accept_3_2 13 39 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  39 137 (Polychromatic418967fa.accept_10_2_9_7_1_720 12 39 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 137 (Polychromatic418967fa.accept_15_11_9_2_1_4780 11 39 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 137 (accept_3_2 10 39 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 137 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 39 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 39 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 137 (accept_3_2 7 39 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  137 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 39 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 137 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 39 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 137 (accept_3_2 4 39 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 137 (Polychromatic418967fa.accept_16_3_7_9_1_3474 3 39 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 39
  137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 137 (accept_3_2 1 39 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 137))))))))))))))))))))))))))))))))))))))) (allB_succ 38 137
  (allA_succ_of_accept 37 38 137 (accept_3_2 37 38 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  38 137 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 38 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 38 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 38 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 137 (accept_3_2 34 38 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 38 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 137
  (Polychromatic418967fa.accept_12_8_2_5_1_844 32 38 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 38 137 (accept_3_2 31 38 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  38 137 (Polychromatic418967fa.accept_13_4_12_7_1_2439 30 38 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 38 137 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 38 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 137 (accept_3_2 28 38 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 38 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 38 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 137
  (Polychromatic418967fa.accept_21_5_17_11_1_7021 26 38 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 38 137 (accept_3_2 25 38 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  38 137 (Polychromatic418967fa.accept_13_11_12_7_1_2443 24 38 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 38 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 38 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 137 (accept_3_2 22 38 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 38 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 137
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 38 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 38 137 (accept_3_2 19 38 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  38 137 (Polychromatic418967fa.accept_13_5_12_7_1_1080 18 38 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 38 137 (Polychromatic418967fa.accept_13_4_12_7_1_2439 17 38 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 137 (accept_3_2 16 38 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 38 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 137
  (Polychromatic418967fa.accept_17_14_4_1_1_3341 14 38 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 38 137 (accept_3_2 13 38 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  38 137 (Polychromatic418967fa.accept_22_12_16_5_1_7020 12 38 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 38 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 38 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 137 (accept_3_2 10 38 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 38 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 137
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 38 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 137 (accept_3_2 7 38 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  137 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 38 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 38 137 (Polychromatic418967fa.accept_10_5_8_7_1_2174 5 38 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 137 (accept_3_2 4 38 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 38 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 38 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 137 (Polychromatic418967fa.accept_16_2_6_9_1_3473 2
  38 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 137 (accept_3_2 1 38 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 137)))))))))))))))))))))))))))))))))))))) (allB_succ 37 137
  (allA_of_3_0 37 37 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 36 137 (allA_succ_of_accept 35 36 137
  (Polychromatic418967fa.accept_22_13_14_5_1_5370 35 36 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 36 137 (accept_3_2 34 36 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  36 137 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 36 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 36 137 (Polychromatic418967fa.accept_14_4_8_11_1_794 32 36 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 137 (accept_3_2 31 36 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 36 137 (Polychromatic418967fa.accept_11_8_3_5_1_355 30 36 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 36 137
  (Polychromatic418967fa.accept_8_5_4_1_1_111 29 36 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 36 137 (accept_3_2 28 36 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  36 137 (Polychromatic418967fa.accept_15_12_6_2_1_2760 27 36 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 36 137 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 36 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 137 (accept_3_2 25 36 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 36 137 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 36 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 36 137
  (Polychromatic418967fa.accept_10_3_6_7_1_2188 23 36 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 36 137 (accept_3_2 22 36 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  36 137 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 36 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 36 137 (Polychromatic418967fa.accept_17_3_2_1_1_1367 20 36 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 137 (accept_3_2 19 36 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 137 (Polychromatic418967fa.accept_14_4_8_11_1_794 18 36 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 36 137
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 36 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 36 137 (accept_3_2 16 36 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  36 137 (Polychromatic418967fa.accept_24_15_12_17_1_7019 15 36 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 36 137 (Polychromatic418967fa.accept_16_14_4_9_1_1646 14 36 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 137 (accept_3_2 13 36 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 36 137 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 36 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 36 137
  (Polychromatic418967fa.accept_10_1_6_7_1_710 11 36 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 36 137 (accept_3_2 10 36 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  36 137 (Polychromatic418967fa.accept_21_9_15_11_1_7018 9 36 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 36 137 (Polychromatic418967fa.accept_11_8_3_5_1_355 8 36 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 137 (accept_3_2 7 36 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 36 137 (Polychromatic418967fa.accept_17_6_2_1_1_3350 6 36 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 36 137
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 36 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 36 137 (accept_3_2 4 36 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 36
  137 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 36 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 36 137 (Polychromatic418967fa.accept_19_2_17_4_1_1856 2 36 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 137 (accept_3_2 1 36 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 36 137)))))))))))))))))))))))))))))))))))) (allB_succ 35 137 (allA_succ_of_accept 34 35 137
  (accept_3_2 34 35 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 137
  (Polychromatic418967fa.accept_9_6_8_2_1_410 33 35 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 137 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 35 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 137 (accept_3_2 31 35 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 35 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 35 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 137 (Polychromatic418967fa.accept_13_3_9_7_1_1730
  29 35 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 137 (accept_3_2 28
  35 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 137
  (Polychromatic418967fa.accept_15_12_5_2_1_2786 27 35 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 35 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 35 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 137 (accept_3_2 25 35 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 35 137 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 35 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 137 (Polychromatic418967fa.accept_9_5_8_2_1_409 23
  35 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 137 (accept_3_2 22 35
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 137
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 35 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 35 137 (Polychromatic418967fa.accept_18_2_17_11_1_3178 20 35 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 35 137 (accept_3_2 19 35 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 35 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 35 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 137 (Polychromatic418967fa.accept_13_4_9_7_1_2402
  17 35 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 137 (accept_3_2 16
  35 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 137
  (Polychromatic418967fa.accept_9_6_8_2_1_410 15 35 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 35 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 35 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 137 (accept_3_2 13 35 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 35 137 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 35 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 137 (Polychromatic418967fa.accept_13_11_9_7_1_2484
  11 35 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 137 (accept_3_2 10
  35 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 35 137
  (Polychromatic418967fa.accept_19_9_16_4_1_5584 9 35 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 35 137 (Polychromatic418967fa.accept_10_8_5_7_1_358 8 35 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 137 (accept_3_2 7 35 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 35 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 35 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 137 (Polychromatic418967fa.accept_9_5_8_2_1_409 5
  35 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 137 (accept_3_2 4 35 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 137 (Polychromatic418967fa.accept_9_3_8_2_1_162 3
  35 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 137
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 35 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 35 137 (accept_3_2 1 35 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35
  137))))))))))))))))))))))))))))))))))) (allB_succ 34 137 (allA_of_3_0 34 34 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 33 137 (allA_succ_of_accept 32 33 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 33 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 137 (accept_3_2 31 33 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 137 (Polychromatic418967fa.accept_7_2_5_4_1_115 30
  33 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 137
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 33 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 33 137 (accept_3_2 28 33 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  33 137 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 33 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 33 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 33 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 137 (accept_3_2 25 33 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 33 137 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 33 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 137
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 33 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 33 137 (accept_3_2 22 33 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  33 137 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 33 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 33 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 33 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 137 (accept_3_2 19 33 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 137 (Polychromatic418967fa.accept_16_2_1_9_1_2577 18 33 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 137
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 33 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 137 (accept_3_2 16 33 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  33 137 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 33 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 33 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 33 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 137 (accept_3_2 13 33 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 137 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 33 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 137
  (Polychromatic418967fa.accept_23_11_10_22_1_7017 11 33 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 33 137 (accept_3_2 10 33 137 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 33 137 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 33 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 33 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 137 (accept_3_2 7 33 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 137 (Polychromatic418967fa.accept_7_6_5_4_1_297 6
  33 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 137
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 33 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 33 137 (accept_3_2 4 33 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33
  137 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 33 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 33 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 33 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 137 (accept_3_2 1 33 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 33 137))))))))))))))))))))))))))))))))) (allB_succ 32 137 (allA_succ_of_accept 31 32 137
  (accept_3_2 31 32 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 32 137
  (Polychromatic418967fa.accept_9_3_5_2_1_28 30 32 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 32 137 (Polychromatic418967fa.accept_10_9_2_7_1_1096 29 32 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 137 (accept_3_2 28 32 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 32 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 32 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 137 (Polychromatic418967fa.accept_9_8_5_2_1_422 26
  32 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 32 137 (accept_3_2 25 32
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 32 137
  (Polychromatic418967fa.accept_9_6_5_2_1_421 24 32 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 32 137 (Polychromatic418967fa.accept_18_5_14_11_1_2073 23 32 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 137 (accept_3_2 22 32 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 32 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 32 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 137 (Polychromatic418967fa.accept_17_3_15_1_1_3348
  20 32 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 32 137 (accept_3_2 19
  32 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 32 137
  (Polychromatic418967fa.accept_25_18_7_12_1_7016 18 32 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 32 137 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 32 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 32 137 (accept_3_2 16 32 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 32 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 32 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 32 137 (Polychromatic418967fa.accept_10_4_2_7_1_373
  14 32 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 32 137 (accept_3_2 13
  32 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 32 137
  (Polychromatic418967fa.accept_9_3_5_2_1_28 12 32 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 32 137 (Polychromatic418967fa.accept_24_11_8_17_1_7015 11 32 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 137 (accept_3_2 10 32 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 32 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 32 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 137 (Polychromatic418967fa.accept_9_8_5_2_1_422 8
  32 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 32 137 (accept_3_2 7 32 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32 137 (Polychromatic418967fa.accept_9_6_5_2_1_421 6
  32 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 32 137
  (Polychromatic418967fa.accept_10_5_2_7_1_345 5 32 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 32 137 (accept_3_2 4 32 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 32
  137 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 32 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 32 137 (Polychromatic418967fa.accept_12_2_8_5_1_408 2 32 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 137 (accept_3_2 1 32 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 32 137)))))))))))))))))))))))))))))))) (allB_succ 31 137 (allA_of_3_0 31 31 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 30 137 (allA_succ_of_accept 29 30 137
  (Polychromatic418967fa.accept_13_3_4_7_1_1711 29 30 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 30 137 (accept_3_2 28 30 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  30 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 30 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 30 137 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 30 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 30 137 (accept_3_2 25 30 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 30 137 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 30 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 30 137
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 30 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 30 137 (accept_3_2 22 30 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  30 137 (Polychromatic418967fa.accept_16_5_14_9_1_2572 21 30 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 30 137 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 30 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 137 (accept_3_2 19 30 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 137 (Polychromatic418967fa.accept_19_18_11_4_1_7014 18 30 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 30 137
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 30 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 30 137 (accept_3_2 16 30 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  30 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 30 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 30 137 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 30 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 137 (accept_3_2 13 30 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 137 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 30 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 30 137
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 30 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 30 137 (accept_3_2 10 30 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  30 137 (Polychromatic418967fa.accept_13_9_4_7_1_1694 9 30 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 30 137 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 30 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 137 (accept_3_2 7 30 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 30 137 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 30 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 30 137
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 30 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 30 137 (accept_3_2 4 30 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 30
  137 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 30 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 30 137 (Polychromatic418967fa.accept_11_2_8_5_1_1219 2 30 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 137 (accept_3_2 1 30 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 30 137)))))))))))))))))))))))))))))) (allB_succ 29 137 (allA_succ_of_accept 28 29 137
  (accept_3_2 28 29 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 137
  (Polychromatic418967fa.accept_13_1_3_7_1_1710 27 29 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 137 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 29 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 137 (accept_3_2 25 29 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 137 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 29 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 137 (Polychromatic418967fa.accept_13_10_3_7_1_2517
  23 29 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 137 (accept_3_2 22
  29 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 137
  (Polychromatic418967fa.accept_13_8_3_7_1_2455 21 29 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 29 137 (Polychromatic418967fa.accept_8_4_5_1_1_299 20 29 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 137 (accept_3_2 19 29 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 29 137 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 29 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 137 (Polychromatic418967fa.accept_7_3_1_4_1_121 17
  29 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 137 (accept_3_2 16 29
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 137
  (Polychromatic418967fa.accept_17_15_12_1_1_3365 15 29 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 29 137 (Polychromatic418967fa.accept_13_1_3_7_1_1710 14 29 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 137 (accept_3_2 13 29 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 29 137 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 29 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 137 (Polychromatic418967fa.accept_13_11_3_7_1_2513
  11 29 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 137 (accept_3_2 10
  29 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 29 137
  (Polychromatic418967fa.accept_11_9_7_5_1_749 9 29 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 29 137 (Polychromatic418967fa.accept_10_8_9_7_1_1118 8 29 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 137 (accept_3_2 7 29 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 29 137 (Polychromatic418967fa.accept_16_6_13_9_1_4690 6 29 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 137 (Polychromatic418967fa.accept_7_5_1_4_1_122 5
  29 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 137 (accept_3_2 4 29 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29 137 (Polychromatic418967fa.accept_7_3_1_4_1_121 3
  29 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 137
  (Polychromatic418967fa.accept_10_2_9_7_1_720 2 29 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 29 137 (accept_3_2 1 29 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29
  137))))))))))))))))))))))))))))) (allB_succ 28 137 (allA_of_3_0 28 28 137 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 27 137 (allA_succ_of_accept 26 27 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 27 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 137 (accept_3_2 25 27 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 137 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 27 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 137
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 27 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 27 137 (accept_3_2 22 27 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  27 137 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 27 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 27 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 27 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 137 (accept_3_2 19 27 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 27 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 27 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 137
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 27 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 27 137 (accept_3_2 16 27 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  27 137 (Polychromatic418967fa.accept_18_15_9_11_1_4371 15 27 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 27 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 27 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 137 (accept_3_2 13 27 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 27 137 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 27 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 137
  (Polychromatic418967fa.accept_13_11_1_7_1_1691 11 27 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 27 137 (accept_3_2 10 27 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  27 137 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 27 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 27 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 27 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 137 (accept_3_2 7 27 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 27 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 27 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 137
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 27 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 27 137 (accept_3_2 4 27 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27
  137 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 27 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 27 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 27 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 137 (accept_3_2 1 27 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 27 137))))))))))))))))))))))))))) (allB_succ 26 137 (allA_succ_of_accept 25 26 137 (accept_3_2
  25 26 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 26 137
  (Polychromatic418967fa.accept_9_6_8_2_1_410 24 26 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 26 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 26 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 26 137 (accept_3_2 22 26 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 26 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 26 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 26 137 (Polychromatic418967fa.accept_7_6_5_4_1_297 20
  26 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 26 137 (accept_3_2 19 26
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 26 137
  (Polychromatic418967fa.accept_21_18_5_11_1_7013 18 26 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 26 137 (Polychromatic418967fa.accept_16_1_10_9_1_4645 17 26 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 26 137 (accept_3_2 16 26 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 26 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 26 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 26 137 (Polychromatic418967fa.accept_9_5_8_2_1_409 14
  26 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 26 137 (accept_3_2 13 26
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 26 137
  (Polychromatic418967fa.accept_9_3_8_2_1_162 12 26 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 26 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 26 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 26 137 (accept_3_2 10 26 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 26 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 26 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 26 137 (Polychromatic418967fa.accept_7_1_5_4_1_134 8
  26 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 26 137 (accept_3_2 7 26 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 26 137 (Polychromatic418967fa.accept_7_6_5_4_1_297 6
  26 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 26 137
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 26 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 26 137 (accept_3_2 4 26 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 26
  137 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 26 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 26 137 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 26 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 26 137 (accept_3_2 1 26 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 26 137)))))))))))))))))))))))))) (allB_succ 25 137 (allA_of_3_0 25 25 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 24 137 (allA_succ_of_accept 23 24 137 (Polychromatic418967fa.accept_9_5_6_2_1_161 23
  24 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 137 (accept_3_2 22 24
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 24 137
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 24 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 24 137 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 24 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 24 137 (accept_3_2 19 24 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 24 137 (Polychromatic418967fa.accept_13_5_11_7_1_559 18 24 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 24 137 (Polychromatic418967fa.accept_9_8_6_2_1_744 17
  24 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 137 (accept_3_2 16 24
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 24 137
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 24 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 24 137 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 24 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 137 (accept_3_2 13 24 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 24 137 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 24 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 24 137 (Polychromatic418967fa.accept_10_1_4_7_1_374
  11 24 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 24 137 (accept_3_2 10
  24 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 24 137
  (Polychromatic418967fa.accept_13_9_11_7_1_1077 9 24 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 24 137 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 24 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 137 (accept_3_2 7 24 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 24 137 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 24 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 24 137 (Polychromatic418967fa.accept_9_5_6_2_1_161 5
  24 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24 137 (accept_3_2 4 24 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 24 137 (Polychromatic418967fa.accept_9_3_6_2_1_160 3
  24 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 24 137
  (Polychromatic418967fa.accept_10_2_4_7_1_352 2 24 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 24 137 (accept_3_2 1 24 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24
  137)))))))))))))))))))))))) (allB_succ 23 137 (allA_succ_of_accept 22 23 137 (accept_3_2 22 23 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 137 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 23 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 23 137
  (Polychromatic418967fa.accept_7_6_2_4_1_291 20 23 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 23 137 (accept_3_2 19 23 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  23 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 23 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 23 137 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 23 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 137 (accept_3_2 16 23 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 137 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 23 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 137
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 23 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 137 (accept_3_2 13 23 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  23 137 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 23 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 23 137 (Polychromatic418967fa.accept_24_11_23_17_1_7012 11 23 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 137 (accept_3_2 10 23 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 137 (Polychromatic418967fa.accept_15_9_8_2_1_1109 9 23 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 137
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 23 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 23 137 (accept_3_2 7 23 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23
  137 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 23 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 23 137 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 23 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 137 (accept_3_2 4 23 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 23 137 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 23 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 23
  137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 137 (accept_3_2 1 23 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23 137))))))))))))))))))))))) (allB_succ 22 137 (allA_of_3_0 22 22
  137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 21 137 (allA_succ_of_accept 20 21 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 21 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 137 (accept_3_2 19 21 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  21 137 (Polychromatic418967fa.accept_14_4_7_11_1_790 18 21 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 21 137 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 21 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 137 (accept_3_2 16 21 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 137 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 21 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 21 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 21 137 (accept_3_2 13 21 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  21 137 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 21 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 21 137 (Polychromatic418967fa.accept_15_11_6_2_1_1106 11 21 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 137 (accept_3_2 10 21 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 137 (Polychromatic418967fa.accept_13_9_8_7_1_1073 9 21 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 21 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 137 (accept_3_2 7 21 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21
  137 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 21 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 137 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 21 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 137 (accept_3_2 4 21 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 21 137 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 21 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 21
  137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 137 (accept_3_2 1 21 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 137))))))))))))))))))))) (allB_succ 20 137 (allA_succ_of_accept
  19 20 137 (accept_3_2 19 20 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 20 137
  (Polychromatic418967fa.accept_11_7_9_5_1_338 18 20 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 20 137 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 20 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 137 (accept_3_2 16 20 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 20 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 20 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 20 137 (Polychromatic418967fa.accept_12_2_8_5_1_408
  14 20 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 20 137 (accept_3_2 13
  20 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 20 137
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 20 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 20 137 (Polychromatic418967fa.accept_15_11_5_2_1_520 11 20 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 20 137 (accept_3_2 10 20 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 20 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 20 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 137 (Polychromatic418967fa.accept_16_8_4_9_1_4666 8
  20 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 20 137 (accept_3_2 7 20 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20 137 (Polychromatic418967fa.accept_17_6_3_1_1_7011 6
  20 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 20 137
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 20 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 20 137 (accept_3_2 4 20 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 20
  137 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 20 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 20 137 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 20 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 20 137 (accept_3_2 1 20 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 137)))))))))))))))))))) (allB_succ 19 137 (allA_of_3_0 19 19 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 18 137 (allA_succ_of_accept 17 18 137 (Polychromatic418967fa.accept_16_1_2_9_1_1607 17 18 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 137 (accept_3_2 16 18 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 18 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 15
  18 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 137
  (Polychromatic418967fa.accept_15_14_3_2_1_2811 14 18 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 18 137 (accept_3_2 13 18 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  18 137 (Polychromatic418967fa.accept_13_12_5_7_1_1696 12 18 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 18 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 18 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 137 (accept_3_2 10 18 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 18 137 (Polychromatic418967fa.accept_10_9_8_7_1_714 9 18 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 137
  (Polychromatic418967fa.accept_14_8_4_11_1_3035 8 18 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 18 137 (accept_3_2 7 18 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18
  137 (Polychromatic418967fa.accept_16_6_2_9_1_5897 6 18 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 18 137 (Polychromatic418967fa.accept_10_5_8_7_1_2174 5 18 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 137 (accept_3_2 4 18 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 18 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 18 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 18 137
  (Polychromatic418967fa.accept_13_2_5_7_1_1695 2 18 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 18 137 (accept_3_2 1 18 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18
  137)))))))))))))))))) (allB_succ 17 137 (allA_succ_of_accept 16 17 137 (accept_3_2 16 17 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 137 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 17 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 137
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 17 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 137 (accept_3_2 13 17 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  17 137 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 17 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 137 (Polychromatic418967fa.accept_13_11_4_7_1_2419 11 17 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 137 (accept_3_2 10 17 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 137 (Polychromatic418967fa.accept_13_9_4_7_1_1694 9 17 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 137
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 17 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 137 (accept_3_2 7 17 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  137 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 17 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 17 137 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 17 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 137 (accept_3_2 4 17 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 17 137 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 17 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 137 (Polychromatic418967fa.accept_16_2_1_9_1_2577 2
  17 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 137 (accept_3_2 1 17 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17 137))))))))))))))))) (allB_succ 16 137 (allA_of_3_0 16 16 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15 137 (allA_succ_of_accept 14 15 137
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 15 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 137 (accept_3_2 13 15 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  15 137 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 15 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 15 137 (Polychromatic418967fa.accept_19_11_15_4_1_7010 11 15 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 137 (accept_3_2 10 15 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 137 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 15 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 15 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 15 137 (accept_3_2 7 15 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15
  137 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 15 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 137 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 15 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 137 (accept_3_2 4 15 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 15 137 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 15 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 15
  137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 137 (accept_3_2 1 15 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 137))))))))))))))) (allB_succ 14 137 (allA_succ_of_accept 13 14
  137 (accept_3_2 13 14 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 14 137
  (Polychromatic418967fa.accept_9_3_5_2_1_28 12 14 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 14 137 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 14 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 14 137 (accept_3_2 10 14 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 14 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 14 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 14 137 (Polychromatic418967fa.accept_9_8_5_2_1_422 8
  14 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 14 137 (accept_3_2 7 14 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 14 137 (Polychromatic418967fa.accept_9_6_5_2_1_421 6
  14 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 14 137
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 5 14 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 14 137 (accept_3_2 4 14 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 14
  137 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 14 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 14 137 (Polychromatic418967fa.accept_10_2_4_7_1_352 2 14 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 14 137 (accept_3_2 1 14 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 14 137)))))))))))))) (allB_succ 13 137 (allA_of_3_0 13 13 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 12 137 (allA_succ_of_accept 11 12 137 (Polychromatic418967fa.accept_13_11_12_7_1_2443 11 12 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 137 (accept_3_2 10 12 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 12 137 (Polychromatic418967fa.accept_7_2_5_4_1_115 9
  12 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 137
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 12 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 12 137 (accept_3_2 7 12 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12
  137 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 12 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 12 137 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 12 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 137 (accept_3_2 4 12 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 12 137 (Polychromatic418967fa.accept_15_3_12_2_1_507 3 12 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 12 137 (Polychromatic418967fa.accept_7_2_5_4_1_115 2
  12 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12 137 (accept_3_2 1 12 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 137)))))))))))) (allB_succ 11 137 (allA_succ_of_accept 10 11 137
  (accept_3_2 10 11 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 137
  (Polychromatic418967fa.accept_13_9_11_7_1_1077 9 11 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 137 (Polychromatic418967fa.accept_17_8_11_1_1_5761 8 11 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 137 (accept_3_2 7 11 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 11 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 137 (Polychromatic418967fa.accept_13_5_11_7_1_559 5
  11 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 137 (accept_3_2 4 11 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 137 (Polychromatic418967fa.accept_13_3_11_7_1_2488
  3 11 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 137
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 11 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 137 (accept_3_2 1 11 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  137))))))))))) (allB_succ 10 137 (allA_of_3_0 10 10 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 9 137
  (allA_succ_of_accept 8 9 137 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 9 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 137 (accept_3_2 7 9 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 9 137 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 9 137 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 137 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 9
  137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 137 (accept_3_2 4 9 137
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 137 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 9
  137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 137
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 9 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 9 137 (accept_3_2 1 9 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 137)))))))))
  (allB_succ 8 137 (allA_succ_of_accept 7 8 137 (accept_3_2 7 8 137 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 8 137 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 8 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 8 137 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 8 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 8 137 (accept_3_2 4 8 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 8 137 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 8 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 8 137
  (Polychromatic418967fa.accept_11_2_8_5_1_1219 2 8 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 8 137 (accept_3_2 1 8 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 137))))))))
  (allB_succ 7 137 (allA_of_3_0 7 7 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 6 137 (allA_succ_of_accept 5
  6 137 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 6 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 137 (accept_3_2 4 6 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 6 137
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 6 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 6 137 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 6 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 137 (accept_3_2 1 6 137 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 6 137)))))) (allB_succ 5 137 (allA_succ_of_accept 4 5 137 (accept_3_2 4 5 137 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 137 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 5 137
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 137
  (Polychromatic418967fa.accept_7_2_5_4_1_115 2 5 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 5 137 (accept_3_2 1 5 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 137)))))
  (allB_succ 4 137 (allA_of_3_0 4 4 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 3 137 (allA_succ_of_accept 2
  3 137 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 3 137 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 3 137 (accept_3_2 1 3 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 137)))
  (allB_succ 2 137 (allA_succ_of_accept 1 2 137 (accept_3_2 1 2 137 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2
  137)) (allB_two
  137)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


