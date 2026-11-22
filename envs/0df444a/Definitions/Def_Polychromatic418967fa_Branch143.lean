-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch143
-- name    : Polychromatic418967fa_Branch143
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:14:22.684647+00:00
-- url     : https://prove2.me/theorems/b206e72a-ab35-40e6-a74a-d22dc494a4c9
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

def Polychromatic418967fa.branch_143 : allB 143 143 :=
  allB_succ' 2 142 143 (Eq.refl Bool.true) (allA_of_3_0 2 142 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  141 143 (Eq.refl Bool.true) (allA_succ_of_accept 2 141 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 141 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 143 (accept_3_2 1 141 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 141 143))) (allB_succ' 4 140 143 (Eq.refl Bool.true)
  (allA_succ_of_accept 3 140 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 140 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 140 143 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 140 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 140 143 (accept_3_2 1 140 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140 143)))) (allB_succ' 5 139 143 (Eq.refl Bool.true) (allA_of_3_0
  5 139 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 6 138 143 (Eq.refl Bool.true) (allA_succ_of_accept 5
  138 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 138 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 138 143 (accept_3_2 4 138 143 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 138 143 (Polychromatic418967fa.accept_19_3_5_10_1_6033 3 138 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 138 143 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 138 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 138 143 (accept_3_2 1 138 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138 143)))))) (allB_succ' 7 137 143 (Eq.refl Bool.true)
  (allA_succ_of_accept 6 137 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 137 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 137 143 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 137 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 143 (accept_3_2 4 137 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 137 143 (Polychromatic418967fa.accept_9_3_2_8_1_108 3
  137 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 137 143
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 137 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 137 143 (accept_3_2 1 137 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 137 143)))))))
  (allB_succ' 8 136 143 (Eq.refl Bool.true) (allA_of_3_0 8 136 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  9 135 143 (Eq.refl Bool.true) (allA_succ_of_accept 8 135 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 135 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 143 (accept_3_2 7 135 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 135 143 (Polychromatic418967fa.accept_7_6_2_3_1_107 6
  135 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 135 143
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 135 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 135 143 (accept_3_2 4 135 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  135 143 (Polychromatic418967fa.accept_16_3_7_15_1_1130 3 135 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 135 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 135 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 143 (accept_3_2 1 135 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 135 143))))))))) (allB_succ' 10 134 143 (Eq.refl Bool.true) (allA_succ_of_accept 9 134
  143 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 134 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 134 143 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 134 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 134 143 (accept_3_2 7 134 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 134 143 (Polychromatic418967fa.accept_15_6_14_8_1_245 6 134 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 134 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 5
  134 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 134 143 (accept_3_2 4 134
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 134 143 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 134 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 134 143
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 134 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 134 143 (accept_3_2 1 134 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134
  143)))))))))) (allB_succ' 11 133 143 (Eq.refl Bool.true) (allA_of_3_0 11 133 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 132 143 (Eq.refl Bool.true) (allA_succ_of_gcd 11 132 143 11 1 12 13 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 132 143 (accept_3_2 10 132 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 132 143 (Polychromatic418967fa.accept_7_2_6_3_1_100 9
  132 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 132 143
  (Polychromatic418967fa.accept_16_8_4_15_1_2941 8 132 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 132 143 (accept_3_2 7 132 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  132 143 (Polychromatic418967fa.accept_17_6_13_7_1_272 6 132 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 132 143 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 132 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 132 143 (accept_3_2 4 132 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 132 143 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 132 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 132 143
  (Polychromatic418967fa.accept_7_2_6_3_1_100 2 132 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 132 143 (accept_3_2 1 132 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132
  143)))))))))))) (allB_succ' 13 131 143 (Eq.refl Bool.true) (allA_succ_of_accept 12 131 143
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 131 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 131 143 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 131 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 131 143 (accept_3_2 10 131 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 131 143 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 131 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 131 143 (Polychromatic418967fa.accept_7_1_5_3_1_268 8
  131 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 131 143 (accept_3_2 7 131
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 131 143
  (Polychromatic418967fa.accept_9_6_5_8_1_598 6 131 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 131 143 (Polychromatic418967fa.accept_15_5_11_8_1_1391 5 131 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 131 143 (accept_3_2 4 131 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 131 143 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 131 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 131 143 (Polychromatic418967fa.accept_7_2_5_3_1_98 2
  131 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 131 143 (accept_3_2 1 131
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 131 143))))))))))))) (allB_succ' 14 130 143 (Eq.refl Bool.true)
  (allA_of_3_0 14 130 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 15 129 143 (Eq.refl Bool.true)
  (allA_succ_of_accept 14 129 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 129 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 143 (accept_3_2 13 129 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 129 143 (Polychromatic418967fa.accept_20_12_9_3_1_5999 12 129 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 129 143
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 129 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 129 143 (accept_3_2 10 129 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  129 143 (Polychromatic418967fa.accept_19_9_15_10_1_7443 9 129 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 129 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 129 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 143 (accept_3_2 7 129 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 129 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 129 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 129 143
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 129 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 129 143 (accept_3_2 4 129 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  129 143 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 129 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 129 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 129 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 143 (accept_3_2 1 129 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 129 143))))))))))))))) (allB_succ' 16 128 143 (Eq.refl Bool.true) (allA_succ_of_accept
  15 128 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 128 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 128 143 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 128 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 128 143 (accept_3_2 13 128 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 128 143 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 128 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 128 143
  (Polychromatic418967fa.accept_10_1_8_3_1_947 11 128 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 128 143 (accept_3_2 10 128 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  128 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 128 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 128 143 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 128 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 128 143 (accept_3_2 7 128 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 128 143 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 128 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 128 143
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 128 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 128 143 (accept_3_2 4 128 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  128 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 128 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 128 143 (Polychromatic418967fa.accept_12_2_8_11_1_31 2 128 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 128 143 (accept_3_2 1 128 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 128 143)))))))))))))))) (allB_succ' 17 127 143 (Eq.refl Bool.true) (allA_of_3_0 17 127
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 18 126 143 (Eq.refl Bool.true) (allA_succ_of_accept 17 126
  143 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 126 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 126 143 (accept_3_2 16 126 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 126 143 (Polychromatic418967fa.accept_22_15_16_11_1_546 15 126 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 126 143 (Polychromatic418967fa.accept_15_14_6_8_1_1410 14 126 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 126 143 (accept_3_2 13 126 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 126 143 (Polychromatic418967fa.accept_24_12_6_23_1_7490 12 126
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 126 143
  (Polychromatic418967fa.accept_19_11_12_10_1_7480 11 126 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 126 143 (accept_3_2 10 126 143 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 126 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 126 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 126 143 (Polychromatic418967fa.accept_10_8_6_3_1_1394 8 126 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 126 143 (accept_3_2 7 126 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 126 143
  (Polychromatic418967fa.accept_19_6_12_10_1_4683 6 126 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 126 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 126 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 126 143 (accept_3_2 4 126 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 126 143 (Polychromatic418967fa.accept_19_3_12_10_1_6015 3 126 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 126 143
  (Polychromatic418967fa.accept_15_2_6_8_1_754 2 126 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 126 143 (accept_3_2 1 126 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  143)))))))))))))))))) (allB_succ' 19 125 143 (Eq.refl Bool.true) (allA_succ_of_accept 18 125 143
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 125 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 125 143 (Polychromatic418967fa.accept_10_7_5_3_1_542 17 125 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 125 143 (accept_3_2 16 125 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 125 143 (Polychromatic418967fa.accept_19_15_11_10_1_2206 15 125 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 125 143
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 125 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 125 143 (accept_3_2 13 125 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 125 143 (Polychromatic418967fa.accept_10_2_5_3_1_1408 12 125 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 125 143 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 125 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 125 143 (accept_3_2 10 125 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 125 143 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 125 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 125 143
  (Polychromatic418967fa.accept_10_8_5_3_1_543 8 125 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 125 143 (accept_3_2 7 125 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  125 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 125 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 125 143 (Polychromatic418967fa.accept_19_5_11_10_1_3347 5 125 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 125 143 (accept_3_2 4 125 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 125 143 (Polychromatic418967fa.accept_15_3_5_8_1_1387 3 125 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 125 143
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 125 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 125 143 (accept_3_2 1 125 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 125
  143))))))))))))))))))) (allB_succ' 20 124 143 (Eq.refl Bool.true) (allA_of_3_0 20 124 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 21 123 143 (Eq.refl Bool.true) (allA_succ_of_accept 20 123 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 123 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 123 143 (accept_3_2 19 123 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 123 143 (Polychromatic418967fa.accept_19_18_9_10_1_4698 18 123 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 123 143 (Polychromatic418967fa.accept_16_1_11_15_1_498 17 123 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 123 143 (accept_3_2 16 123 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 123 143 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 123 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 123 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 123 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 123 143 (accept_3_2 13 123 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 123 143 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 123 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 123 143 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 123 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 123 143 (accept_3_2 10 123 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 123 143 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 123 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 123 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 123 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 123 143 (accept_3_2 7 123 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  123 143 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 123 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 123 143 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 123 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 143 (accept_3_2 4 123 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 123 143 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 123 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 123 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 123 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 123 143 (accept_3_2 1 123 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 123
  143))))))))))))))))))))) (allB_succ' 22 122 143 (Eq.refl Bool.true) (allA_succ_of_accept 21 122 143
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 122 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 122 143 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 122 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 122 143 (accept_3_2 19 122 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 122 143 (Polychromatic418967fa.accept_19_18_8_10_1_7489 18 122 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 122 143
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 122 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 122 143 (accept_3_2 16 122 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 122 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 122 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 122 143 (Polychromatic418967fa.accept_16_14_10_15_1_3969 14 122 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 122 143 (accept_3_2 13 122 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 122 143 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 122 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 122 143
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 122 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 122 143 (accept_3_2 10 122 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  122 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 122 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 122 143 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 122 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 122 143 (accept_3_2 7 122 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 122 143 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 122 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 122 143
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 122 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 122 143 (accept_3_2 4 122 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  122 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 122 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 122 143 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 122 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 122 143 (accept_3_2 1 122 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 122 143)))))))))))))))))))))) (allB_succ' 23 121 143 (Eq.refl Bool.true) (allA_of_3_0
  23 121 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 120 143 (Eq.refl Bool.true) (allA_succ_of_accept 23
  120 143 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 120 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 120 143 (accept_3_2 22 120 143 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 120 143 (Polychromatic418967fa.accept_19_2_6_10_1_3364 21 120 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 120 143 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 120 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 120 143 (accept_3_2 19 120 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 120 143 (Polychromatic418967fa.accept_7_4_1_3_1_277
  18 120 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 120 143
  (Polychromatic418967fa.accept_16_1_8_15_1_1945 17 120 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 120 143 (accept_3_2 16 120 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 120 143 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 120 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 120 143 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 120 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 120 143 (accept_3_2 13 120 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 120 143 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 120 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 120 143
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 120 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 120 143 (accept_3_2 10 120 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  120 143 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 120 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 120 143 (Polychromatic418967fa.accept_17_8_1_7_1_7488 8 120 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 120 143 (accept_3_2 7 120 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 120 143 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 120 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 120 143
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 120 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 120 143 (accept_3_2 4 120 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  120 143 (Polychromatic418967fa.accept_21_3_15_17_1_7487 3 120 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 120 143 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 120 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 120 143 (accept_3_2 1 120 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 120 143)))))))))))))))))))))))) (allB_succ' 25 119 143 (Eq.refl Bool.true)
  (allA_succ_of_accept 24 119 143 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 119 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 119 143 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 119 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 119 143 (accept_3_2 22 119 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 119 143 (Polychromatic418967fa.accept_9_3_2_8_1_108
  21 119 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 119 143
  (Polychromatic418967fa.accept_15_5_14_8_1_1376 20 119 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 119 143 (accept_3_2 19 119 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 119 143 (Polychromatic418967fa.accept_14_4_7_3_1_1718 18 119 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 119 143 (Polychromatic418967fa.accept_22_17_9_11_1_7407 17 119 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 119 143 (accept_3_2 16 119 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 119 143 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 119 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 119 143
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 119 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 119 143 (accept_3_2 13 119 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 119 143 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 119 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 119 143 (Polychromatic418967fa.accept_14_11_7_3_1_3416 11 119 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 143 (accept_3_2 10 119 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 119 143 (Polychromatic418967fa.accept_15_9_14_8_1_1396 9 119
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 143
  (Polychromatic418967fa.accept_16_8_7_15_1_6339 8 119 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 119 143 (accept_3_2 7 119 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  119 143 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 119 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 119 143 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 119 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 143 (accept_3_2 4 119 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 119 143 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 119 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 143
  (Polychromatic418967fa.accept_18_2_11_17_1_4773 2 119 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 119 143 (accept_3_2 1 119 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  143))))))))))))))))))))))))) (allB_succ' 26 118 143 (Eq.refl Bool.true) (allA_of_3_0 26 118 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 27 117 143 (Eq.refl Bool.true) (allA_succ_of_gcd 26 117 143 13 2 9 11 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 117 143 (accept_3_2 25
  117 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 117 143
  (Polychromatic418967fa.accept_10_4_7_3_1_54 24 117 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 117 143 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 117 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 143 (accept_3_2 22 117 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 117 143 (Polychromatic418967fa.accept_22_21_7_11_1_7486 21 117 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 117 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 117 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 117 143 (accept_3_2 19 117 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 117 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 117 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 117 143 (Polychromatic418967fa.accept_16_1_5_15_1_2918 17 117 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 143 (accept_3_2 16 117 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 117 143 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 117 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 143
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 117 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 13 117 143 13 1 9 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 12 117 143 (Polychromatic418967fa.accept_14_12_5_3_1_1011 12 117 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 117 143 (Polychromatic418967fa.accept_15_11_12_8_1_739 11 117
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 143 (accept_3_2 10 117
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 143 (Polychromatic418967fa.accept_7_2_5_3_1_98
  9 117 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 117 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 117 143 (accept_3_2 7 117 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  117 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 117 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 117 143 (Polychromatic418967fa.accept_10_5_7_3_1_561 5 117 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 143 (accept_3_2 4 117 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 117 143 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 117 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 143
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 117 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 117 143 (accept_3_2 1 117 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  143))))))))))))))))))))))))))) (allB_succ' 28 116 143 (Eq.refl Bool.true) (allA_succ_of_accept 27 116 143
  (Polychromatic418967fa.accept_6_3_2_5_1_32 27 116 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 116 143 (Polychromatic418967fa.accept_12_2_8_11_1_31 26 116 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 116 143 (accept_3_2 25 116 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 116 143 (Polychromatic418967fa.accept_16_8_4_15_1_2941 24 116 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 116 143
  (Polychromatic418967fa.accept_17_6_14_7_1_6115 23 116 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 116 143 (accept_3_2 22 116 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 116 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 116 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 116 143 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 116 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 116 143 (accept_3_2 19 116 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 116 143 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 116 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 116 143
  (Polychromatic418967fa.accept_10_7_6_3_1_927 17 116 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 116 143 (accept_3_2 16 116 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 116 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 116 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 116 143 (Polychromatic418967fa.accept_12_2_8_11_1_31 14 116 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 116 143 (accept_3_2 13 116 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 116 143 (Polychromatic418967fa.accept_15_12_11_8_1_1392 12 116
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 116 143
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 116 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 116 143 (accept_3_2 10 116 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  116 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 116 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 116 143 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 116 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 116 143 (accept_3_2 7 116 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 116 143 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 116 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 116 143
  (Polychromatic418967fa.accept_15_5_11_8_1_1391 5 116 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 116 143 (accept_3_2 4 116 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  116 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 116 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 116 143 (Polychromatic418967fa.accept_12_2_8_11_1_31 2 116 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 116 143 (accept_3_2 1 116 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 116 143)))))))))))))))))))))))))))) (allB_succ' 29 115 143 (Eq.refl Bool.true)
  (allA_of_3_0 29 115 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 30 114 143 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 114 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 114 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 114 143 (accept_3_2 28 114 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 114 143 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 114 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 114 143 (Polychromatic418967fa.accept_7_5_2_3_1_106
  26 114 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 114 143 (accept_3_2 25
  114 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 114 143
  (Polychromatic418967fa.accept_20_4_14_3_1_3181 24 114 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 114 143 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 114 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 114 143 (accept_3_2 22 114 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 114 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 114 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 114 143 (Polychromatic418967fa.accept_7_6_2_3_1_107
  20 114 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 114 143 (accept_3_2 19
  114 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 114 143
  (Polychromatic418967fa.accept_15_3_9_8_1_3164 18 114 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 114 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 114 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 114 143 (accept_3_2 16 114 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 114 143 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 114 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 114 143 (Polychromatic418967fa.accept_9_5_6_8_1_101
  14 114 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 114 143 (accept_3_2 13
  114 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 114 143
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 114 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 114 143 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 114 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 114 143 (accept_3_2 10 114 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 114 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 114 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 114 143 (Polychromatic418967fa.accept_7_1_2_3_1_257 8
  114 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 114 143 (accept_3_2 7 114
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 114 143
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 114 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 114 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 114 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 114 143 (accept_3_2 4 114 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 114 143 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 114 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 114 143 (Polychromatic418967fa.accept_9_2_6_8_1_321 2
  114 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 114 143 (accept_3_2 1 114
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114 143)))))))))))))))))))))))))))))) (allB_succ' 31 113 143
  (Eq.refl Bool.true) (allA_succ_of_accept 30 113 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 113 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 113 143
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 113 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 113 143 (accept_3_2 28 113 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 113 143 (Polychromatic418967fa.accept_16_11_1_15_1_1123 27 113 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 113 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 113 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 113 143 (accept_3_2 25 113 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 113 143 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 113 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 113 143
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 113 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 113 143 (accept_3_2 22 113 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 113 143 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 113 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 113 143 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 113 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 113 143 (accept_3_2 19 113 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 113 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 113 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 113 143
  (Polychromatic418967fa.accept_19_17_18_10_1_7485 17 113 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 113 143 (accept_3_2 16 113 143 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 113 143 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 113 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 113 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 113 143 (accept_3_2 13 113 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 113 143 (Polychromatic418967fa.accept_7_5_1_3_1_103
  12 113 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 113 143
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 113 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 113 143 (accept_3_2 10 113 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  113 143 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 113 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 113 143 (Polychromatic418967fa.accept_16_8_1_15_1_1982 8 113 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 113 143 (accept_3_2 7 113 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 113 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 113 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 113 143
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 113 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 113 143 (accept_3_2 4 113 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  113 143 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 113 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 113 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 113 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 113 143 (accept_3_2 1 113 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 113 143))))))))))))))))))))))))))))))) (allB_succ' 32 112 143 (Eq.refl Bool.true)
  (allA_of_3_0 32 112 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 111 143 (Eq.refl Bool.true)
  (allA_succ_of_accept 32 111 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 111 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 143 (accept_3_2 31 111 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 111 143 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 111 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 111 143 (Polychromatic418967fa.accept_9_2_3_8_1_318
  29 111 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 143 (accept_3_2 28
  111 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 111 143
  (Polychromatic418967fa.accept_19_8_16_10_1_7484 27 111 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 111 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 111 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 143 (accept_3_2 25 111 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 143 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 111 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 111 143
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 111 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 111 143 (accept_3_2 22 111 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 111 143 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 111 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 111 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 111 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 143 (accept_3_2 19 111 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 143 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 111 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 143
  (Polychromatic418967fa.accept_15_2_6_8_1_754 17 111 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 111 143 (accept_3_2 16 111 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 111 143 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 111 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 111 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 111 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 143 (accept_3_2 13 111 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 143 (Polychromatic418967fa.accept_10_2_1_3_1_233 12 111 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 143
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 111 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 111 143 (accept_3_2 10 111 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  111 143 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 111 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 111 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 111 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 143 (accept_3_2 7 111 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 143 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 111 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 143
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 111 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 111 143 (accept_3_2 4 111 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  111 143 (Polychromatic418967fa.accept_22_3_1_11_1_7483 3 111 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 111 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 111 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 143 (accept_3_2 1 111 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 111 143))))))))))))))))))))))))))))))))) (allB_succ' 34 110 143 (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 110 143 11 3 10 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 110 143 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 110 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 110 143 (accept_3_2 31 110 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 110 143 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 110 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 110 143
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 110 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 110 143 (accept_3_2 28 110 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 110 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 110 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 110 143 (Polychromatic418967fa.accept_15_11_5_8_1_3157 26 110 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 110 143 (accept_3_2 25 110 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 110 143 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 110 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 110 143
  (Polychromatic418967fa.accept_7_2_5_3_1_98 23 110 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 110 143 11 2 10 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 110 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 110 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 110 143 (Polychromatic418967fa.accept_12_8_2_11_1_246
  20 110 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 110 143 (accept_3_2 19
  110 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 110 143
  (Polychromatic418967fa.accept_15_3_5_8_1_1387 18 110 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 110 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 110 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 110 143 (accept_3_2 16 110 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 110 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 110 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 110 143 (Polychromatic418967fa.accept_9_5_2_8_1_109
  14 110 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 110 143 (accept_3_2 13
  110 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 110 143
  (Polychromatic418967fa.accept_9_3_2_8_1_108 12 110 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 11 110 143 11 1 10 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 10 110 143 (accept_3_2 10 110 143 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 110 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 110 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 110 143 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 110 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 110 143 (accept_3_2 7 110 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 110 143 (Polychromatic418967fa.accept_9_6_2_8_1_592 6
  110 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 110 143
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 110 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 110 143 (accept_3_2 4 110 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  110 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 110 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 110 143 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 110 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 110 143 (accept_3_2 1 110 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 110 143)))))))))))))))))))))))))))))))))) (allB_succ' 35 109 143 (Eq.refl Bool.true)
  (allA_of_3_0 35 109 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 108 143 (Eq.refl Bool.true)
  (allA_succ_of_accept 35 108 143 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 108 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 108 143 (accept_3_2 34 108 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 108 143 (Polychromatic418967fa.accept_17_16_6_7_1_2715 33 108 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 108 143
  (Polychromatic418967fa.accept_23_9_16_5_1_7482 32 108 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 108 143 (accept_3_2 31 108 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 108 143 (Polychromatic418967fa.accept_17_13_6_7_1_4999 30 108 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 108 143 (Polychromatic418967fa.accept_16_13_12_15_1_6290 29 108 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 108 143 (accept_3_2 28 108 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 108 143 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 108 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 108 143
  (Polychromatic418967fa.accept_10_6_8_3_1_930 26 108 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 108 143 (accept_3_2 25 108 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 108 143 (Polychromatic418967fa.accept_15_9_3_8_1_3155 24 108 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 108 143 (Polychromatic418967fa.accept_19_4_13_10_1_7382 23 108 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 108 143 (accept_3_2 22 108 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 108 143 (Polychromatic418967fa.accept_10_1_8_3_1_947 21 108
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 108 143
  (Polychromatic418967fa.accept_14_6_10_3_1_1038 20 108 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 108 143 (accept_3_2 19 108 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 108 143 (Polychromatic418967fa.accept_16_2_12_15_1_2908 18 108 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 108 143 (Polychromatic418967fa.accept_22_17_20_11_1_7481 17 108 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 108 143 (accept_3_2 16 108 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 108 143 (Polychromatic418967fa.accept_10_5_8_3_1_229 15 108
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 108 143
  (Polychromatic418967fa.accept_17_14_6_7_1_4980 14 108 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 108 143 (accept_3_2 13 108 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 108 143 (Polychromatic418967fa.accept_15_12_3_8_1_5245 12 108 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 108 143 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 108 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 108 143 (accept_3_2 10 108 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 108 143 (Polychromatic418967fa.accept_15_9_3_8_1_3155 9 108 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 108 143
  (Polychromatic418967fa.accept_16_8_12_15_1_2005 8 108 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 108 143 (accept_3_2 7 108 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  108 143 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 108 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 108 143 (Polychromatic418967fa.accept_10_5_8_3_1_229 5 108 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 108 143 (accept_3_2 4 108 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 108 143 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 108 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 108 143
  (Polychromatic418967fa.accept_16_2_12_15_1_2908 2 108 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 108 143 (accept_3_2 1 108 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  143)))))))))))))))))))))))))))))))))))) (allB_succ' 37 107 143 (Eq.refl Bool.true) (allA_succ_of_accept 36 107 143
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 107 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 107 143 (Polychromatic418967fa.accept_10_5_7_3_1_561 35 107 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 107 143 (accept_3_2 34 107 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 107 143 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 107 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 107 143
  (Polychromatic418967fa.accept_17_15_5_7_1_2694 32 107 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 107 143 (accept_3_2 31 107 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 107 143 (Polychromatic418967fa.accept_19_11_12_10_1_7480 30 107 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 29 107 143 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 107 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 107 143 (accept_3_2 28 107 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 107 143 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 107 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 107 143
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 107 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 107 143 (accept_3_2 25 107 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 107 143 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 107 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 107 143 (Polychromatic418967fa.accept_16_7_11_15_1_2929 23 107 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 107 143 (accept_3_2 22 107 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 107 143 (Polychromatic418967fa.accept_15_6_2_8_1_2223 21 107
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 107 143
  (Polychromatic418967fa.accept_7_6_2_3_1_107 20 107 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 107 143 (accept_3_2 19 107 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 107 143 (Polychromatic418967fa.accept_27_18_26_8_1_7479 18 107 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 107 143 (Polychromatic418967fa.accept_16_1_11_15_1_498 17 107 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 107 143 (accept_3_2 16 107 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 107 143 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 107 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 143
  (Polychromatic418967fa.accept_10_4_7_3_1_54 14 107 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 107 143 (accept_3_2 13 107 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 107 143 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 107 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 107 143 (Polychromatic418967fa.accept_17_11_5_7_1_6177 11 107 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 143 (accept_3_2 10 107 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 107 143 (Polychromatic418967fa.accept_15_9_2_8_1_1379 9 107 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 143
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 107 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 107 143 (accept_3_2 7 107 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  107 143 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 107 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 107 143 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 107 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 143 (accept_3_2 4 107 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 143 (Polychromatic418967fa.accept_16_3_11_15_1_1963 3 107 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 143
  (Polychromatic418967fa.accept_19_2_12_10_1_7478 2 107 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 107 143 (accept_3_2 1 107 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107
  143))))))))))))))))))))))))))))))))))))) (allB_succ' 38 106 143 (Eq.refl Bool.true) (allA_of_3_0 38 106 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 105 143 (Eq.refl Bool.true) (allA_succ_of_accept 38 105 143
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 105 143 (accept_3_2 37 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 105 143 (Polychromatic418967fa.accept_24_12_9_23_1_7477 36 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 105 143 (Polychromatic418967fa.accept_20_15_5_3_1_1953 35 105 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 105 143 (accept_3_2 34 105 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 105 143 (Polychromatic418967fa.accept_17_16_3_7_1_5028 33 105
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 105 143 (accept_3_2 31 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 105 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 105 143 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 105 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 143 (accept_3_2 28 105 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 105 143 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 105 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 143
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 105 143 (accept_3_2 25 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 105 143 (Polychromatic418967fa.accept_14_10_7_3_1_1022 24 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 105 143 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 105 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 143 (accept_3_2 22 105 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 105 143 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 105 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 105 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 105 143 (accept_3_2 19 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 105 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 105 143 (Polychromatic418967fa.accept_10_7_5_3_1_542 17 105 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 143 (accept_3_2 16 105 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 105 143 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 105
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 105 143
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 105 143 (accept_3_2 13 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 105 143 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 105 143 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 105 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 105 143 (accept_3_2 10 105 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 105 143 (Polychromatic418967fa.accept_18_9_15_17_1_3497 9 105 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 105 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 105 143 (accept_3_2 7 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  105 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 105 143 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 105 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 143 (accept_3_2 4 105 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 143 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 105 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 143
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 105 143 (accept_3_2 1 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  143))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 104 143 (Eq.refl Bool.true) (allA_succ_of_gcd 39 104 143 13
  3 8 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 104 143
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 104 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 104 143 (accept_3_2 37 104 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 104 143 (Polychromatic418967fa.accept_15_6_14_8_1_245 36 104 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 104 143 (Polychromatic418967fa.accept_15_5_14_8_1_1376 35 104 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 104 143 (accept_3_2 34 104 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 104 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 104 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 104 143
  (Polychromatic418967fa.accept_7_4_6_3_1_271 32 104 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 104 143 (accept_3_2 31 104 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 104 143 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 104 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 104 143 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 104 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 104 143 (accept_3_2 28 104 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 104 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 104 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 104 143 13 2 8 11 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 104 143 (accept_3_2 25 104 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 104 143 (Polychromatic418967fa.accept_9_6_5_8_1_598
  24 104 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 104 143
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 104 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 104 143 (accept_3_2 22 104 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 104 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 104 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 104 143 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 104 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 104 143 (accept_3_2 19 104 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 104 143 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 104 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 104 143
  (Polychromatic418967fa.accept_10_7_4_3_1_560 17 104 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 104 143 (accept_3_2 16 104 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 104 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 104 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 104 143 (Polychromatic418967fa.accept_12_2_8_11_1_31 14 104 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13 104 143 13 1 8 11 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12 104 143
  (Polychromatic418967fa.accept_9_3_5_8_1_99 12 104 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 104 143 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 104 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 104 143 (accept_3_2 10 104 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 104 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 104 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 104 143
  (Polychromatic418967fa.accept_21_8_20_17_1_7455 8 104 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 104 143 (accept_3_2 7 104 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  104 143 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 104 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 104 143 (Polychromatic418967fa.accept_15_5_14_8_1_1376 5 104 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 104 143 (accept_3_2 4 104 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 104 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 104 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 104 143
  (Polychromatic418967fa.accept_7_2_6_3_1_100 2 104 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 104 143 (accept_3_2 1 104 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  143)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 103 143 (Eq.refl Bool.true) (allA_of_3_0 41 103 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 102 143 (Eq.refl Bool.true) (allA_succ_of_accept 41 102 143
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 102 143 (accept_3_2 40 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 102 143 (Polychromatic418967fa.accept_16_7_6_15_1_495 39 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 102 143 (Polychromatic418967fa.accept_9_2_3_8_1_318 38 102 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 102 143 (accept_3_2 37 102 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 102 143 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 102 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 102 143
  (Polychromatic418967fa.accept_10_5_2_3_1_239 35 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 102 143 (accept_3_2 34 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 102 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 102 143 (Polychromatic418967fa.accept_9_5_3_8_1_316 32 102 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 102 143 (accept_3_2 31 102 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 102 143 (Polychromatic418967fa.accept_20_10_2_3_1_7425 30 102 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 102 143
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 102 143 (accept_3_2 28 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 102 143 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 102 143 (Polychromatic418967fa.accept_15_11_12_8_1_739 26 102 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 102 143 (accept_3_2 25 102 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 102 143 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 102 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 102 143
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 102 143 (accept_3_2 22 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 102 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 102 143 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 102 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 102 143 (accept_3_2 19 102 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 102 143 (Polychromatic418967fa.accept_15_3_12_8_1_738 18 102 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 102 143
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 102 143 (accept_3_2 16 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 102 143 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 102 143 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 102 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 102 143 (accept_3_2 13 102 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 102 143 (Polychromatic418967fa.accept_22_12_14_11_1_5874 12 102 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 102 143
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 102 143 (accept_3_2 10 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  102 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 102 143 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 102 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 102 143 (accept_3_2 7 102 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 102 143 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 102 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 102 143
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 102 143 (accept_3_2 4 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  102 143 (Polychromatic418967fa.accept_15_3_12_8_1_738 3 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 102 143 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 102 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 102 143 (accept_3_2 1 102 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 102 143)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 101 143 (Eq.refl
  Bool.true) (allA_succ_of_accept 42 101 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 101 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 101 143 (Polychromatic418967fa.accept_9_5_2_8_1_109
  41 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 101 143 (accept_3_2 40
  101 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 101 143
  (Polychromatic418967fa.accept_9_3_2_8_1_108 39 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 101 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 101 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 101 143 (accept_3_2 37 101 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 101 143 (Polychromatic418967fa.accept_16_4_5_15_1_5083 36 101 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 101 143
  (Polychromatic418967fa.accept_15_5_11_8_1_1391 35 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 101 143 (accept_3_2 34 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 101 143 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 101 143 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 101 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 101 143 (accept_3_2 31 101 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 101 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 101 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 101 143
  (Polychromatic418967fa.accept_26_3_23_13_1_7476 29 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 101 143 (accept_3_2 28 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 101 143 (Polychromatic418967fa.accept_15_12_11_8_1_1392 27 101 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 101 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 26
  101 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 101 143 (accept_3_2 25
  101 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 101 143
  (Polychromatic418967fa.accept_9_6_2_8_1_592 24 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 101 143 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 101 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 101 143 (accept_3_2 22 101 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 101 143 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 101 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 101 143
  (Polychromatic418967fa.accept_15_5_11_8_1_1391 20 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 101 143 (accept_3_2 19 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 101 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 101 143 (Polychromatic418967fa.accept_16_1_5_15_1_2918 17 101 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 143 (accept_3_2 16 101 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 101 143 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 101 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 101 143
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 101 143 (accept_3_2 13 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 101 143 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 101 143 (Polychromatic418967fa.accept_24_11_5_23_1_5706 11 101 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 143 (accept_3_2 10 101 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 101 143 (Polychromatic418967fa.accept_19_9_6_10_1_7430 9 101
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 143
  (Polychromatic418967fa.accept_10_8_1_3_1_1374 8 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 101 143 (accept_3_2 7 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  101 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 101 143 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 101 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 143 (accept_3_2 4 101 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 143 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 101 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 143
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 101 143 (accept_3_2 1 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101
  143))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 100 143 (Eq.refl Bool.true) (allA_of_3_0 44 100 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 99 143 (Eq.refl Bool.true) (allA_succ_of_gcd 44 99 143 11 4 9
  13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 99 143
  (accept_3_2 43 99 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 99 143
  (Polychromatic418967fa.accept_17_8_14_7_1_6203 42 99 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 99 143 (Polychromatic418967fa.accept_23_18_7_5_1_7475 41 99 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 143 (accept_3_2 40 99 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 99 143 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 99 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 99 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 38
  99 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 99 143 (accept_3_2 37 99
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 99 143
  (Polychromatic418967fa.accept_8_4_3_7_1_491 36 99 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 99 143 (Polychromatic418967fa.accept_19_16_4_10_1_7474 35 99 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 143 (accept_3_2 34 99 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 33 99 143 11 3 9 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 99 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 99 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 143 (accept_3_2 31 99 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 99 143 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 99 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 143
  (Polychromatic418967fa.accept_15_14_9_8_1_3165 29 99 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 99 143 (accept_3_2 28 99 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  99 143 (Polychromatic418967fa.accept_16_11_3_15_1_1989 27 99 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 99 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 99 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 143 (accept_3_2 25 99 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 99 143 (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 99 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 99 143
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 99 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 99 143 11 2 9 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 99 143 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 99 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 99 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 99 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 99 143 (accept_3_2 19 99 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 99 143 (Polychromatic418967fa.accept_7_4_1_3_1_277 18
  99 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 143
  (Polychromatic418967fa.accept_15_2_9_8_1_736 17 99 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 99 143 (accept_3_2 16 99 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  99 143 (Polychromatic418967fa.accept_18_15_9_17_1_6043 15 99 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 99 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 99 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 143 (accept_3_2 13 99 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 99 143 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 99 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 11 99 143 11 1 9 13 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 99 143 (accept_3_2 10 99 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 143 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 99 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 99 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 99 143 (accept_3_2 7 99 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99
  143 (Polychromatic418967fa.accept_10_6_9_3_1_935 6 99 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 99 143 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 99 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 143 (accept_3_2 4 99 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 99 143 (Polychromatic418967fa.accept_15_3_9_8_1_3164 3 99 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 99
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 143 (accept_3_2 1 99 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99 143))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46
  98 143 (Eq.refl Bool.true) (allA_succ_of_accept 45 98 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 98 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 98 143
  (Polychromatic418967fa.accept_12_8_2_11_1_246 44 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 98 143 (accept_3_2 43 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  98 143 (Polychromatic418967fa.accept_20_2_18_3_1_4519 42 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 98 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 98 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 98 143 (accept_3_2 40 98 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 98 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 98 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 98 143
  (Polychromatic418967fa.accept_18_2_8_17_1_4754 38 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 98 143 (accept_3_2 37 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  98 143 (Polychromatic418967fa.accept_10_6_8_3_1_930 36 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 98 143 (Polychromatic418967fa.accept_10_5_8_3_1_229 35 98 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 98 143 (accept_3_2 34 98 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 98 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 98 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 98 143
  (Polychromatic418967fa.accept_12_8_2_11_1_246 32 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 98 143 (accept_3_2 31 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  98 143 (Polychromatic418967fa.accept_19_11_3_10_1_3354 30 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 98 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 98 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 98 143 (accept_3_2 28 98 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 98 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 98 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 98 143
  (Polychromatic418967fa.accept_10_6_8_3_1_930 26 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 98 143 (accept_3_2 25 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  98 143 (Polychromatic418967fa.accept_19_5_3_10_1_4641 24 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 98 143 (Polychromatic418967fa.accept_17_6_13_7_1_272 23 98 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 98 143 (accept_3_2 22 98 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 98 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 98 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 98 143
  (Polychromatic418967fa.accept_12_8_2_11_1_246 20 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 98 143 (accept_3_2 19 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  98 143 (Polychromatic418967fa.accept_21_18_14_17_1_7473 18 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 98 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 98 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 98 143 (accept_3_2 16 98 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 98 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 98 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 98 143
  (Polychromatic418967fa.accept_22_14_10_11_1_7472 14 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 98 143 (accept_3_2 13 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 98 143 (Polychromatic418967fa.accept_16_12_2_15_1_490 12 98 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 98 143 (Polychromatic418967fa.accept_10_1_8_3_1_947 11 98 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 98 143 (accept_3_2 10 98 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 98 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 98
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 98 143
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 98 143 (accept_3_2 7 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 98
  143 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 98 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 98 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 98 143 (accept_3_2 4 98 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 98 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 98 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 98 143 (Polychromatic418967fa.accept_17_2_13_7_1_5011
  2 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 98 143 (accept_3_2 1 98
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98 143))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 47 97 143 (Eq.refl Bool.true) (allA_of_3_0 47 97 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  48 96 143 (Eq.refl Bool.true) (allA_succ_of_accept 47 96 143 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 96 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 96 143 (accept_3_2 46 96 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 96 143 (Polychromatic418967fa.accept_19_7_1_10_1_4702
  45 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 96 143
  (Polychromatic418967fa.accept_7_2_5_3_1_98 44 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 96 143 (accept_3_2 43 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  96 143 (Polychromatic418967fa.accept_19_4_1_10_1_7447 42 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 96 143 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 96 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 96 143 (accept_3_2 40 96 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 96 143 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 96 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 96 143
  (Polychromatic418967fa.accept_9_2_6_8_1_321 38 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 96 143 (accept_3_2 37 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  96 143 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 96 143 (Polychromatic418967fa.accept_17_1_11_7_1_4962 35 96 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 96 143 (accept_3_2 34 96 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 96 143 (Polychromatic418967fa.accept_14_5_12_3_1_3397 33 96
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 96 143
  (Polychromatic418967fa.accept_9_5_6_8_1_101 32 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 96 143 (accept_3_2 31 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  96 143 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 96 143 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 96 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 96 143 (accept_3_2 28 96 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 96 143 (Polychromatic418967fa.accept_10_7_6_3_1_927 27 96 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 96 143
  (Polychromatic418967fa.accept_19_7_1_10_1_4702 26 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 96 143 (accept_3_2 25 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  96 143 (Polychromatic418967fa.accept_21_3_12_17_1_7471 24 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 96 143 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 96 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 96 143 (accept_3_2 22 96 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 96 143 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 96 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 96 143
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 96 143 (accept_3_2 19 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  96 143 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 96 143 (Polychromatic418967fa.accept_10_7_6_3_1_927 17 96 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 96 143 (accept_3_2 16 96 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 96 143 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 96 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 96 143
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 96 143 (accept_3_2 13 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  96 143 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 96 143 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 96 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 96 143 (accept_3_2 10 96 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 96 143 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 96 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 96 143
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 96 143 (accept_3_2 7 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 96
  143 (Polychromatic418967fa.accept_19_6_1_10_1_7449 6 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 96 143 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 96 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 96 143 (accept_3_2 4 96 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 96 143 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 96 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 96 143
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 96 143 (accept_3_2 1 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  143)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 95 143 (Eq.refl Bool.true) (allA_succ_of_accept 48
  95 143 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 95 143 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 95 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 95 143 (accept_3_2 46 95 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 95 143 (Polychromatic418967fa.accept_20_5_15_3_1_4516 45 95 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 95 143
  (Polychromatic418967fa.accept_15_14_5_8_1_3175 44 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 95 143 (accept_3_2 43 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  95 143 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 95 143 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 95 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 95 143 (accept_3_2 40 95 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 95 143 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 95 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 95 143
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 95 143 (accept_3_2 37 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  95 143 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 95 143 (Polychromatic418967fa.accept_14_7_11_3_1_5365 35 95 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 95 143 (accept_3_2 34 95 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 95 143 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 95 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 95 143
  (Polychromatic418967fa.accept_10_2_5_3_1_1408 32 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 95 143 (accept_3_2 31 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  95 143 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 95 143 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 95 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 95 143 (accept_3_2 28 95 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 95 143 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 95 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 95 143
  (Polychromatic418967fa.accept_15_11_5_8_1_3157 26 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 95 143 (accept_3_2 25 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  95 143 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 95 143 (Polychromatic418967fa.accept_21_2_11_17_1_4395 23 95 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 95 143 (accept_3_2 22 95 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 95 143 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 95 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 95 143
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 95 143 (accept_3_2 19 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  95 143 (Polychromatic418967fa.accept_10_8_5_3_1_543 18 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 95 143 (Polychromatic418967fa.accept_10_7_5_3_1_542 17 95 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 95 143 (accept_3_2 16 95 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 95 143 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 95 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 95 143
  (Polychromatic418967fa.accept_15_14_5_8_1_3175 14 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 95 143 (accept_3_2 13 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  95 143 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 95 143 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 95 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 95 143 (accept_3_2 10 95 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 95 143 (Polychromatic418967fa.accept_20_9_15_3_1_7470 9 95 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 95 143
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 95 143 (accept_3_2 7 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 95
  143 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 95 143 (Polychromatic418967fa.accept_20_5_15_3_1_4516 5 95 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 95 143 (accept_3_2 4 95 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 95 143 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 95 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 95 143 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 95
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 143 (accept_3_2 1 95 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 95 143))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  50 94 143 (Eq.refl Bool.true) (allA_of_3_0 50 94 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 93 143
  (Eq.refl Bool.true) (allA_succ_of_accept 50 93 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 93 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 93 143 (accept_3_2 49 93 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 93 143 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 93 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 93 143
  (Polychromatic418967fa.accept_7_5_2_3_1_106 47 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 93 143 (accept_3_2 46 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  93 143 (Polychromatic418967fa.accept_19_7_17_10_1_4630 45 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 93 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 93 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 93 143 (accept_3_2 43 93 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 93 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 93 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 93 143
  (Polychromatic418967fa.accept_7_6_2_3_1_107 41 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 93 143 (accept_3_2 40 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  93 143 (Polychromatic418967fa.accept_12_3_9_11_1_231 39 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 93 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 93 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 93 143 (accept_3_2 37 93 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 93 143 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 93 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 93 143
  (Polychromatic418967fa.accept_15_5_3_8_1_748 35 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 93 143 (accept_3_2 34 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  93 143 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 93 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 93 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 93 143 (accept_3_2 31 93 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 93 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 93 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 93 143
  (Polychromatic418967fa.accept_7_1_2_3_1_257 29 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 93 143 (accept_3_2 28 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  93 143 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 93 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 93 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 93 143 (accept_3_2 25 93 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 93 143 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 93 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 93 143
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 93 143 (accept_3_2 22 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  93 143 (Polychromatic418967fa.accept_17_4_8_7_1_7469 21 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 93 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 93 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 143 (accept_3_2 19 93 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 93 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 93 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 143
  (Polychromatic418967fa.accept_22_17_5_11_1_2772 17 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 93 143 (accept_3_2 16 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  93 143 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 93 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 93 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 143 (accept_3_2 13 93 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 93 143 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 93 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 143
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 93 143 (accept_3_2 10 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  93 143 (Polychromatic418967fa.accept_15_9_3_8_1_3155 9 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 93 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 93 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 143 (accept_3_2 7 93 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 93 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 93 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 143
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 93 143 (accept_3_2 4 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93
  143 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 93 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 93 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 143 (accept_3_2 1 93 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 93 143))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 92 143
  (Eq.refl Bool.true) (allA_succ_of_accept 51 92 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 92 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 92 143
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 92 143 (accept_3_2 49 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  92 143 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 92 143 (Polychromatic418967fa.accept_7_5_1_3_1_103 47 92 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 92 143 (accept_3_2 46 92 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 92 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 92 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 92 143
  (Polychromatic418967fa.accept_7_2_1_3_1_102 44 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 92 143 (accept_3_2 43 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  92 143 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 92 143 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 92 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 92 143 (accept_3_2 40 92 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 92 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 92 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 92 143
  (Polychromatic418967fa.accept_12_2_8_11_1_31 38 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 92 143 (accept_3_2 37 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  92 143 (Polychromatic418967fa.accept_15_6_2_8_1_2223 36 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 92 143 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 92 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 92 143 (accept_3_2 34 92 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 92 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 92 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 92 143
  (Polychromatic418967fa.accept_7_4_1_3_1_277 32 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 92 143 (accept_3_2 31 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  92 143 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 92 143 (Polychromatic418967fa.accept_16_13_12_15_1_6290 29 92 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 92 143 (accept_3_2 28 92 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 92 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 92 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 92 143
  (Polychromatic418967fa.accept_7_5_1_3_1_103 26 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 92 143 (accept_3_2 25 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  92 143 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 92 143 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 92 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 92 143 (accept_3_2 22 92 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 92 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 92 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 92 143
  (Polychromatic418967fa.accept_16_4_12_15_1_6289 20 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 92 143 (accept_3_2 19 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  92 143 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 92 143 (Polychromatic418967fa.accept_22_17_4_11_1_7403 17 92 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 92 143 (accept_3_2 16 92 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 92 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 92 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 92 143
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 92 143 (accept_3_2 13 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  92 143 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 92 143 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 92 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 92 143 (accept_3_2 10 92 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 92 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 92 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 92 143
  (Polychromatic418967fa.accept_16_8_12_15_1_2005 8 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 92 143 (accept_3_2 7 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 92
  143 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 92 143 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 92 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 92 143 (accept_3_2 4 92 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 92 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 92 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 92 143 (Polychromatic418967fa.accept_7_2_1_3_1_102 2
  92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 143 (accept_3_2 1 92 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92 143))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 53 91 143 (Eq.refl Bool.true) (allA_of_3_0 53 91 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  54 90 143 (Eq.refl Bool.true) (allA_succ_of_accept 53 90 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 90 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 90 143 (accept_3_2 52 90 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 90 143 (Polychromatic418967fa.accept_7_2_6_3_1_100 51
  90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 90 143
  (Polychromatic418967fa.accept_19_12_14_10_1_4625 50 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 90 143 (accept_3_2 49 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 90 143 (Polychromatic418967fa.accept_26_22_12_13_1_7468 48 90 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 90 143 (Polychromatic418967fa.accept_20_7_10_3_1_949 47 90 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 90 143 (accept_3_2 46 90 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 90 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 45
  90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 90 143
  (Polychromatic418967fa.accept_7_2_6_3_1_100 44 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 90 143 (accept_3_2 43 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  90 143 (Polychromatic418967fa.accept_19_4_14_10_1_7467 42 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 90 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 90 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 90 143 (accept_3_2 40 90 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 90 143 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 90 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 90 143
  (Polychromatic418967fa.accept_14_10_6_3_1_1055 38 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 90 143 (accept_3_2 37 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  90 143 (Polychromatic418967fa.accept_21_15_6_17_1_7466 36 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 90 143 (Polychromatic418967fa.accept_20_15_10_3_1_7465 35 90 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 90 143 (accept_3_2 34 90 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 90 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 90 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 90 143
  (Polychromatic418967fa.accept_7_4_6_3_1_271 32 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 90 143 (accept_3_2 31 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  90 143 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 90 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 90 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 90 143 (accept_3_2 28 90 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 90 143 (Polychromatic418967fa.accept_16_11_10_15_1_6301 27 90 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 90 143
  (Polychromatic418967fa.accept_17_9_5_7_1_3802 26 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 90 143 (accept_3_2 25 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  90 143 (Polychromatic418967fa.accept_14_10_6_3_1_1055 24 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 90 143 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 90 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 90 143 (accept_3_2 22 90 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 90 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 90 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 90 143
  (Polychromatic418967fa.accept_19_1_14_10_1_4619 20 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 90 143 (accept_3_2 19 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  90 143 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 90 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 90 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 90 143 (accept_3_2 16 90 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 90 143 (Polychromatic418967fa.accept_17_15_5_7_1_2694 15 90 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 90 143
  (Polychromatic418967fa.accept_16_14_10_15_1_3969 14 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 90 143 (accept_3_2 13 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 90 143 (Polychromatic418967fa.accept_17_12_5_7_1_6179 12 90 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 90 143 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 90 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 90 143 (accept_3_2 10 90 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 90 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 90
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 90 143
  (Polychromatic418967fa.accept_22_8_2_11_1_7464 8 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 90 143 (accept_3_2 7 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 90
  143 (Polychromatic418967fa.accept_19_6_14_10_1_4624 6 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 90 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 90 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 90 143 (accept_3_2 4 90 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 90 143 (Polychromatic418967fa.accept_22_3_2_11_1_7463 3 90 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 90 143
  (Polychromatic418967fa.accept_7_2_6_3_1_100 2 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 90 143 (accept_3_2 1 90 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  143)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 89 143 (Eq.refl Bool.true)
  (allA_succ_of_accept 54 89 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 89 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 143 (Polychromatic418967fa.accept_21_11_5_17_1_760 53 89
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 89 143 (accept_3_2 52 89 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 89 143 (Polychromatic418967fa.accept_7_2_5_3_1_98 51
  89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 89 143
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 89 143 (accept_3_2 49 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  89 143 (Polychromatic418967fa.accept_17_14_4_7_1_7439 48 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 89 143 (Polychromatic418967fa.accept_19_9_13_10_1_4601 47 89 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 89 143 (accept_3_2 46 89 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 89 143 (Polychromatic418967fa.accept_25_20_14_18_1_7462 45 89
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 89 143
  (Polychromatic418967fa.accept_7_2_5_3_1_98 44 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 89 143 (accept_3_2 43 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  89 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 89 143 (Polychromatic418967fa.accept_19_3_13_10_1_7461 41 89 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 89 143 (accept_3_2 40 89 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 89 143 (Polychromatic418967fa.accept_15_9_14_8_1_1396 39 89
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 89 143
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 89 143 (accept_3_2 37 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  89 143 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 89 143 (Polychromatic418967fa.accept_15_5_14_8_1_1376 35 89 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 89 143 (accept_3_2 34 89 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 89 143 (Polychromatic418967fa.accept_21_12_5_17_1_7460 33 89
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 89 143
  (Polychromatic418967fa.accept_20_12_9_3_1_5999 32 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 89 143 (accept_3_2 31 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  89 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 89 143 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 89 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 89 143 (accept_3_2 28 89 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 89 143 (Polychromatic418967fa.accept_39_27_11_26_1_7459 27 89 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 89 143
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 89 143 (accept_3_2 25 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  89 143 (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 89 143 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 89 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 89 143 (accept_3_2 22 89 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 89 143 (Polychromatic418967fa.accept_15_6_14_8_1_245 21 89 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 89 143
  (Polychromatic418967fa.accept_15_5_14_8_1_1376 20 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 89 143 (accept_3_2 19 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  89 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 89 143 (Polychromatic418967fa.accept_23_17_20_5_1_7458 17 89 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 89 143 (accept_3_2 16 89 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 89 143 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 89 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 89 143
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 89 143 (accept_3_2 13 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  89 143 (Polychromatic418967fa.accept_14_12_5_3_1_1011 12 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 89 143 (Polychromatic418967fa.accept_21_11_5_17_1_760 11 89 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 89 143 (accept_3_2 10 89 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 89 143 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 89 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 89 143
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 89 143 (accept_3_2 7 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 89
  143 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 89 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 89 143 (Polychromatic418967fa.accept_15_5_14_8_1_1376 5 89 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 89 143 (accept_3_2 4 89 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 89 143 (Polychromatic418967fa.accept_17_3_4_7_1_1658 3 89 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 89 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 89
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 143 (accept_3_2 1 89 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 89 143)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 56 88 143 (Eq.refl Bool.true) (allA_of_3_0 56 88 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  57 87 143 (Eq.refl Bool.true) (allA_succ_of_accept 56 87 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 87 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 87 143 (accept_3_2 55 87 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 87 143 (Polychromatic418967fa.accept_10_4_7_3_1_54 54
  87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 87 143
  (Polychromatic418967fa.accept_19_15_11_10_1_2206 53 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 87 143 (accept_3_2 52 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 87 143 (Polychromatic418967fa.accept_16_3_7_15_1_1130 51 87 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 87 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 87 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 143 (accept_3_2 49 87 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 87 143 (Polychromatic418967fa.accept_9_3_6_8_1_308 48
  87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 87 143
  (Polychromatic418967fa.accept_9_2_6_8_1_321 47 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 87 143 (accept_3_2 46 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  87 143 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 87 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 87 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 87 143 (accept_3_2 43 87 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 87 143 (Polychromatic418967fa.accept_18_6_15_17_1_7363 42 87 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 87 143
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 87 143 (accept_3_2 40 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  87 143 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 87 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 87 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 87 143 (accept_3_2 37 87 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 87 143 (Polychromatic418967fa.accept_10_6_7_3_1_547 36 87 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 87 143
  (Polychromatic418967fa.accept_10_5_7_3_1_561 35 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 87 143 (accept_3_2 34 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  87 143 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 87 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 87 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 143 (accept_3_2 31 87 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 87 143 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 87 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 143
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 87 143 (accept_3_2 28 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  87 143 (Polychromatic418967fa.accept_16_11_7_15_1_1998 27 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 87 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 87 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 143 (accept_3_2 25 87 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 87 143 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 87 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 143
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 87 143 (accept_3_2 22 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  87 143 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 87 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 87 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 143 (accept_3_2 19 87 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 87 143 (Polychromatic418967fa.accept_15_3_12_8_1_738 18 87 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 143
  (Polychromatic418967fa.accept_23_17_18_5_1_7391 17 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 87 143 (accept_3_2 16 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  87 143 (Polychromatic418967fa.accept_10_5_7_3_1_561 15 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 87 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 87 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 143 (accept_3_2 13 87 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 87 143 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 87 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 143
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 87 143 (accept_3_2 10 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  87 143 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 87 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 87 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 143 (accept_3_2 7 87 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 87 143 (Polychromatic418967fa.accept_10_6_7_3_1_547 6 87 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 143
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 87 143 (accept_3_2 4 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87
  143 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 87 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 87 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 87 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 143 (accept_3_2 1 87 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 87 143))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 86 143 (Eq.refl
  Bool.true) (allA_succ_of_accept 57 86 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 86 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 86 143 (Polychromatic418967fa.accept_9_2_5_8_1_11 56
  86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 86 143 (accept_3_2 55 86
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 86 143
  (Polychromatic418967fa.accept_7_5_2_3_1_106 54 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 86 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 86 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 86 143 (accept_3_2 52 86 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 86 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 86 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 86 143 (Polychromatic418967fa.accept_7_1_2_3_1_257 50
  86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 86 143 (accept_3_2 49 86
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 86 143
  (Polychromatic418967fa.accept_7_6_2_3_1_107 48 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 86 143 (Polychromatic418967fa.accept_7_5_2_3_1_106 47 86 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 86 143 (accept_3_2 46 86 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 86 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 86 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 86 143 (Polychromatic418967fa.accept_12_8_2_11_1_246
  44 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 86 143 (accept_3_2 43
  86 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 86 143
  (Polychromatic418967fa.accept_9_6_5_8_1_598 42 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 86 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 86 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 86 143 (accept_3_2 40 86 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 86 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 86 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 86 143 (Polychromatic418967fa.accept_9_2_5_8_1_11 38
  86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 86 143 (accept_3_2 37 86
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 86 143
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 86 143 (Polychromatic418967fa.accept_15_5_11_8_1_1391 35 86 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 86 143 (accept_3_2 34 86 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 86 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 86 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 86 143 (Polychromatic418967fa.accept_12_8_2_11_1_246
  32 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 86 143 (accept_3_2 31
  86 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 86 143
  (Polychromatic418967fa.accept_9_3_5_8_1_99 30 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 86 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 86 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 86 143 (accept_3_2 28 86 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 86 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 86 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 86 143 (Polychromatic418967fa.accept_7_5_2_3_1_106 26
  86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 86 143 (accept_3_2 25 86
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 86 143
  (Polychromatic418967fa.accept_9_6_5_8_1_598 24 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 86 143 (Polychromatic418967fa.accept_16_7_6_15_1_495 23 86 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 86 143 (accept_3_2 22 86 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 86 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 86 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 86 143 (Polychromatic418967fa.accept_7_6_2_3_1_107 20
  86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 86 143 (accept_3_2 19 86
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 86 143
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 86 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 86 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 86 143 (accept_3_2 16 86 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 86 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 86 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 86 143 (Polychromatic418967fa.accept_21_14_2_17_1_758
  14 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 86 143 (accept_3_2 13
  86 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 86 143
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 86 143 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 86 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 86 143 (accept_3_2 10 86 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 86 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 86 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 143 (Polychromatic418967fa.accept_7_1_2_3_1_257 8
  86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 86 143 (accept_3_2 7 86 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86 143 (Polychromatic418967fa.accept_7_6_2_3_1_107 6
  86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 86 143
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 86 143 (accept_3_2 4 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 86
  143 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 86 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 86 143 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 86 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 86 143 (accept_3_2 1 86 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 86 143)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 85 143 (Eq.refl
  Bool.true) (allA_of_3_0 59 85 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 84 143 (Eq.refl Bool.true)
  (allA_succ_of_accept 59 84 143 (Polychromatic418967fa.accept_8_3_4_7_1_475 59 84 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 84 143 (accept_3_2 58 84 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 84 143 (Polychromatic418967fa.accept_10_7_4_3_1_560 57 84 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 84 143 (Polychromatic418967fa.accept_9_2_3_8_1_318 56
  84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 84 143 (accept_3_2 55 84
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 84 143
  (Polychromatic418967fa.accept_17_3_16_7_1_5014 54 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 84 143 (Polychromatic418967fa.accept_16_5_4_15_1_1102 53 84 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 84 143 (accept_3_2 52 84 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 84 143 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 84 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 84 143 (Polychromatic418967fa.accept_9_5_3_8_1_316 50
  84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 84 143 (accept_3_2 49 84
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 84 143
  (Polychromatic418967fa.accept_15_3_9_8_1_3164 48 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 84 143 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 84 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 84 143 (accept_3_2 46 84 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 84 143 (Polychromatic418967fa.accept_18_9_12_17_1_6060 45 84 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 84 143
  (Polychromatic418967fa.accept_15_14_9_8_1_3165 44 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 84 143 (accept_3_2 43 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  84 143 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 84 143 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 84 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 84 143 (accept_3_2 40 84 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 84 143 (Polychromatic418967fa.accept_10_9_4_3_1_539 39 84 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 84 143
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 84 143 (accept_3_2 37 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  84 143 (Polychromatic418967fa.accept_19_17_8_10_1_7457 36 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 84 143 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 84 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 84 143 (accept_3_2 34 84 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 84 143 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 84 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 84 143
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 84 143 (accept_3_2 31 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  84 143 (Polychromatic418967fa.accept_16_14_4_15_1_3944 30 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 84 143 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 84 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 84 143 (accept_3_2 28 84 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 84 143 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 84 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 84 143
  (Polychromatic418967fa.accept_22_4_18_11_1_5898 26 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 84 143 (accept_3_2 25 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  84 143 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 84 143 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 84 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 84 143 (accept_3_2 22 84 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 84 143 (Polychromatic418967fa.accept_16_5_4_15_1_1102 21 84 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 84 143
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 84 143 (accept_3_2 19 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  84 143 (Polychromatic418967fa.accept_15_3_9_8_1_3164 18 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 84 143 (Polychromatic418967fa.accept_10_7_4_3_1_560 17 84 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 84 143 (accept_3_2 16 84 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 84 143 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 84 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 84 143
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 84 143 (accept_3_2 13 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  84 143 (Polychromatic418967fa.accept_16_12_4_15_1_5091 12 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 84 143 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 84 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 84 143 (accept_3_2 10 84 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 84 143 (Polychromatic418967fa.accept_10_9_4_3_1_539 9 84 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 84 143
  (Polychromatic418967fa.accept_16_8_4_15_1_2941 8 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 84 143 (accept_3_2 7 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 84
  143 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 84 143 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 84 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 84 143 (accept_3_2 4 84 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 84 143 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 84 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 84 143 (Polychromatic418967fa.accept_9_2_3_8_1_318 2
  84 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 143 (accept_3_2 1 84 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84 143))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 61 83 143 (Eq.refl Bool.true) (allA_succ_of_accept 60 83 143 (Polychromatic418967fa.accept_7_4_6_3_1_271
  60 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 143
  (Polychromatic418967fa.accept_9_5_2_8_1_109 59 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 143 (accept_3_2 58 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 143 (Polychromatic418967fa.accept_9_3_2_8_1_108 57 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 143 (Polychromatic418967fa.accept_17_5_15_7_1_4992 56 83 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 143 (accept_3_2 55 83 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 143 (Polychromatic418967fa.accept_19_16_7_10_1_7456 54 83
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 143
  (Polychromatic418967fa.accept_7_4_6_3_1_271 53 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 143 (accept_3_2 52 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 143 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 143 (Polychromatic418967fa.accept_9_5_2_8_1_109 50 83 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 143 (accept_3_2 49 83 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 143 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 83 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 143
  (Polychromatic418967fa.accept_19_9_7_10_1_1170 47 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 143 (accept_3_2 46 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 143 (Polychromatic418967fa.accept_16_13_3_15_1_1931 45 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 143 (Polychromatic418967fa.accept_7_2_6_3_1_100 44 83 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 143 (accept_3_2 43 83 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 143 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 83 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 143
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 143 (accept_3_2 40 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 143 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 143 (Polychromatic418967fa.accept_14_10_13_3_1_2552 38 83 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 143 (accept_3_2 37 83 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 143 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 83 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 143
  (Polychromatic418967fa.accept_19_16_7_10_1_7456 35 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 143 (accept_3_2 34 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 143 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 143 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 83 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 143 (accept_3_2 31 83 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 143 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 83 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 143
  (Polychromatic418967fa.accept_16_13_3_15_1_1931 29 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 143 (accept_3_2 28 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 143 (Polychromatic418967fa.accept_16_11_3_15_1_1989 27 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 143 (Polychromatic418967fa.accept_17_9_15_7_1_6212 26 83 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 143 (accept_3_2 25 83 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 143 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 83 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 143
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 143 (accept_3_2 22 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 143 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 143 (Polychromatic418967fa.accept_8_4_3_7_1_491 20 83 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 143 (accept_3_2 19 83 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 143 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 83 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 143
  (Polychromatic418967fa.accept_19_17_7_10_1_1171 17 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 143 (accept_3_2 16 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 143 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 143 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 83 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 143 (accept_3_2 13 83 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 143 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 83 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 143
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 143 (accept_3_2 10 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 143 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 143 (Polychromatic418967fa.accept_21_8_20_17_1_7455 8 83 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 143 (accept_3_2 7 83 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 143 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 83 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 143
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 143 (accept_3_2 4 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  143 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 83 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 83 143 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 83 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 143 (accept_3_2 1 83 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 143))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 82 143
  (Eq.refl Bool.true) (allA_of_3_0 62 82 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 63 81 143 (Eq.refl
  Bool.true) (allA_succ_of_accept 62 81 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 81 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 143 (accept_3_2 61 81 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 81 143 (Polychromatic418967fa.accept_19_3_5_10_1_6033 60 81 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 143
  (Polychromatic418967fa.accept_15_14_6_8_1_1410 59 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 81 143 (accept_3_2 58 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  81 143 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 81 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 81 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 143 (accept_3_2 55 81 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 81 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 81 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 143
  (Polychromatic418967fa.accept_16_5_1_15_1_3922 53 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 81 143 (accept_3_2 52 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  81 143 (Polychromatic418967fa.accept_12_3_9_11_1_231 51 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 81 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 81 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 81 143 (accept_3_2 49 81 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 81 143 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 81 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 143
  (Polychromatic418967fa.accept_15_2_6_8_1_754 47 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 81 143 (accept_3_2 46 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  81 143 (Polychromatic418967fa.accept_17_11_13_7_1_3795 45 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 81 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 81 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 143 (accept_3_2 43 81 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 81 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 81 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 143
  (Polychromatic418967fa.accept_7_6_4_3_1_266 41 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 81 143 (accept_3_2 40 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  81 143 (Polychromatic418967fa.accept_12_3_9_11_1_231 39 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 81 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 81 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 143 (accept_3_2 37 81 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 81 143 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 81 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 143
  (Polychromatic418967fa.accept_14_7_11_3_1_5365 35 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 81 143 (accept_3_2 34 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  81 143 (Polychromatic418967fa.accept_18_15_9_17_1_6043 33 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 81 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 81 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 143 (accept_3_2 31 81 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 81 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 81 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 143
  (Polychromatic418967fa.accept_7_1_4_3_1_21 29 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 81 143 (accept_3_2 28 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  81 143 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 81 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 81 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 143 (accept_3_2 25 81 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 81 143 (Polychromatic418967fa.accept_16_8_1_15_1_1982 24 81 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 143
  (Polychromatic418967fa.accept_17_6_13_7_1_272 23 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 143 (accept_3_2 22 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  81 143 (Polychromatic418967fa.accept_14_7_11_3_1_5365 21 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 81 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 81 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 143 (accept_3_2 19 81 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 81 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 81 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 143
  (Polychromatic418967fa.accept_15_2_6_8_1_754 17 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 81 143 (accept_3_2 16 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  81 143 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 81 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 81 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 143 (accept_3_2 13 81 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 81 143 (Polychromatic418967fa.accept_10_2_1_3_1_233 12 81 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 143
  (Polychromatic418967fa.accept_16_11_1_15_1_1123 11 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 81 143 (accept_3_2 10 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  81 143 (Polychromatic418967fa.accept_21_9_18_17_1_7454 9 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 81 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 81 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 143 (accept_3_2 7 81 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 81 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 143
  (Polychromatic418967fa.accept_16_5_1_15_1_3922 5 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 143 (accept_3_2 4 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81
  143 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 81 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 81 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 81 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 143 (accept_3_2 1 81 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 81 143))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 80
  143 (Eq.refl Bool.true) (allA_succ_of_accept 63 80 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 80 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 80 143
  (Polychromatic418967fa.accept_12_2_8_11_1_31 62 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 80 143 (accept_3_2 61 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  80 143 (Polychromatic418967fa.accept_23_14_11_5_1_7453 60 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 80 143 (Polychromatic418967fa.accept_15_14_5_8_1_3175 59 80 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 80 143 (accept_3_2 58 80 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 80 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 80 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 80 143
  (Polychromatic418967fa.accept_15_11_5_8_1_3157 56 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 80 143 (accept_3_2 55 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  80 143 (Polychromatic418967fa.accept_17_3_12_7_1_4949 54 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 80 143 (Polychromatic418967fa.accept_17_2_12_7_1_7429 53 80 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 80 143 (accept_3_2 52 80 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 80 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 80 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 80 143
  (Polychromatic418967fa.accept_12_2_8_11_1_31 50 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 80 143 (accept_3_2 49 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  80 143 (Polychromatic418967fa.accept_14_6_10_3_1_1038 48 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 80 143 (Polychromatic418967fa.accept_19_9_4_10_1_7370 47 80 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 80 143 (accept_3_2 46 80 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 80 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 80 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 80 143
  (Polychromatic418967fa.accept_15_14_5_8_1_3175 44 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 80 143 (accept_3_2 43 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  80 143 (Polychromatic418967fa.accept_15_12_5_8_1_5247 42 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 80 143 (Polychromatic418967fa.accept_14_13_10_3_1_1037 41 80 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 80 143 (accept_3_2 40 80 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 80 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 80 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 80 143
  (Polychromatic418967fa.accept_12_2_8_11_1_31 38 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 80 143 (accept_3_2 37 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  80 143 (Polychromatic418967fa.accept_17_2_12_7_1_7429 36 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 80 143 (Polychromatic418967fa.accept_14_7_10_3_1_1034 35 80 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 80 143 (accept_3_2 34 80 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 80 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 80 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 80 143
  (Polychromatic418967fa.accept_19_13_4_10_1_7452 32 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 80 143 (accept_3_2 31 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  80 143 (Polychromatic418967fa.accept_22_8_14_11_1_7451 30 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 80 143 (Polychromatic418967fa.accept_15_14_5_8_1_3175 29 80 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 80 143 (accept_3_2 28 80 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 80 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 80 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 80 143
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 80 143 (accept_3_2 25 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  80 143 (Polychromatic418967fa.accept_22_2_14_11_1_7450 24 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 80 143 (Polychromatic418967fa.accept_18_5_8_17_1_3478 23 80 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 80 143 (accept_3_2 22 80 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 80 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 80 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 80 143
  (Polychromatic418967fa.accept_14_6_10_3_1_1038 20 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 80 143 (accept_3_2 19 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  80 143 (Polychromatic418967fa.accept_15_3_5_8_1_1387 18 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 80 143 (Polychromatic418967fa.accept_19_17_4_10_1_7371 17 80 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 80 143 (accept_3_2 16 80 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 80 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 80 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 80 143
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 80 143 (accept_3_2 13 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  80 143 (Polychromatic418967fa.accept_15_12_5_8_1_5247 12 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 80 143 (Polychromatic418967fa.accept_15_11_5_8_1_3157 11 80 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 80 143 (accept_3_2 10 80 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 80 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 80 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 80 143
  (Polychromatic418967fa.accept_19_8_4_10_1_7393 8 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 80 143 (accept_3_2 7 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 80
  143 (Polychromatic418967fa.accept_14_6_10_3_1_1038 6 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 80 143 (Polychromatic418967fa.accept_17_5_12_7_1_2651 5 80 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 80 143 (accept_3_2 4 80 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 80 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 80 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 80 143
  (Polychromatic418967fa.accept_12_2_8_11_1_31 2 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 80 143 (accept_3_2 1 80 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  143)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 79 143 (Eq.refl Bool.true)
  (allA_of_3_0 65 79 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 66 78 143 (Eq.refl Bool.true)
  (allA_succ_of_gcd 65 78 143 13 5 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 64 78 143 (accept_3_2 64 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  78 143 (Polychromatic418967fa.accept_19_6_2_10_1_4691 63 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 78 143 (Polychromatic418967fa.accept_19_5_2_10_1_3371 62 78 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 143 (accept_3_2 61 78 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 78 143 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 78 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 78 143
  (Polychromatic418967fa.accept_9_5_6_8_1_101 59 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 78 143 (accept_3_2 58 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  78 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 78 143 (Polychromatic418967fa.accept_9_2_6_8_1_321 56 78 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 78 143 (accept_3_2 55 78 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 78 143 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 78 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 78 143
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 78 143 13 4 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 78 143 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 78 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 78 143 (Polychromatic418967fa.accept_9_5_6_8_1_101 50 78 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 143 (accept_3_2 49 78 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 78 143 (Polychromatic418967fa.accept_9_3_6_8_1_308 48
  78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 78 143
  (Polychromatic418967fa.accept_7_5_1_3_1_103 47 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 78 143 (accept_3_2 46 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  78 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 78 143 (Polychromatic418967fa.accept_7_2_1_3_1_102 44 78 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 143 (accept_3_2 43 78 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 78 143 (Polychromatic418967fa.accept_15_12_3_8_1_5245 42 78 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 78 143
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 78 143 (accept_3_2 40 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 78
  143 13 3 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38
  78 143 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 78 143 (accept_3_2 37 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 78 143 (Polychromatic418967fa.accept_10_6_8_3_1_930 36 78 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 78 143 (Polychromatic418967fa.accept_10_5_8_3_1_229 35 78 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 78 143 (accept_3_2 34 78 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 78 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 33
  78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 78 143
  (Polychromatic418967fa.accept_7_4_1_3_1_277 32 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 78 143 (accept_3_2 31 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  78 143 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 78 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 78 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 78 143 (accept_3_2 28 78 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 78 143 (Polychromatic418967fa.accept_15_12_3_8_1_5245 27 78 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 78 143 13 2 6 11 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 78 143 (accept_3_2 25 78 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 78 143 (Polychromatic418967fa.accept_15_9_3_8_1_3155 24 78 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 78 143
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 78 143 (accept_3_2 22 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  78 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 78 143 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 78 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 143 (accept_3_2 19 78 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 78 143 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 78 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 78 143
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 78 143 (accept_3_2 16 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  78 143 (Polychromatic418967fa.accept_10_5_8_3_1_229 15 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 78 143 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 78 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13 78 143 13 1 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12 78 143 (Polychromatic418967fa.accept_7_5_1_3_1_103 12
  78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 78 143
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 78 143 (accept_3_2 10 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  78 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 78 143 (Polychromatic418967fa.accept_19_8_2_10_1_7415 8 78 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 143 (accept_3_2 7 78 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 78 143 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 78 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 78 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 78
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78 143 (accept_3_2 4 78 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 78 143 (Polychromatic418967fa.accept_9_3_6_8_1_308 3
  78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 78 143
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 78 143 (accept_3_2 1 78 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  143)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 77 143 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 77 143 11 6 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 77 143 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 77 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 77 143 (accept_3_2 64 77 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 77 143 (Polychromatic418967fa.accept_19_6_1_10_1_7449 63 77 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 77 143
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 77 143 (accept_3_2 61 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  77 143 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 77 143 (Polychromatic418967fa.accept_23_13_8_5_1_4094 59 77 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 77 143 (accept_3_2 58 77 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 77 143 (Polychromatic418967fa.accept_9_3_5_8_1_99 57 77 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 77 143
  (Polychromatic418967fa.accept_9_2_5_8_1_11 56 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 77 143 11 5 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 77 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 77 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 143 (Polychromatic418967fa.accept_14_11_7_3_1_3416 53 77
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 77 143 (accept_3_2 52 77 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 77 143 (Polychromatic418967fa.accept_9_6_5_8_1_598 51
  77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 77 143
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 77 143 (accept_3_2 49 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  77 143 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 77 143 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 77 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 77 143 (accept_3_2 46 77 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 77 143 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 77 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 77 143 11 4 7 13 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 77 143 (accept_3_2 43 77 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 77 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 143
  (Polychromatic418967fa.accept_19_3_1_10_1_2193 41 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 143 (accept_3_2 40 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 143 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 77 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 143 (accept_3_2 37 77 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 143 (Polychromatic418967fa.accept_10_6_7_3_1_547 36 77 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 143
  (Polychromatic418967fa.accept_10_5_7_3_1_561 35 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 143 (accept_3_2 34 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 77
  143 11 3 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32
  77 143 (Polychromatic418967fa.accept_14_4_7_3_1_1718 32 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 77 143 (accept_3_2 31 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 77 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 77 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 143 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 77 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 77 143 (accept_3_2 28 77 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 77 143 (Polychromatic418967fa.accept_23_4_8_5_1_7448
  27 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 77 143
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 77 143 (accept_3_2 25 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  77 143 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 77 143 (Polychromatic418967fa.accept_19_4_1_10_1_7447 23 77 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 77 143 11 2 7 13 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 77 143
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 77 143 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 77 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 143 (accept_3_2 19 77 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 77 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 77 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 143
  (Polychromatic418967fa.accept_19_17_1_10_1_4671 17 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 143 (accept_3_2 16 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 143 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 77 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 143 (accept_3_2 13 77 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 143 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 77 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 11 77 143 11 1 7 13 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 77 143 (accept_3_2 10 77 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 77 143 (Polychromatic418967fa.accept_15_9_2_8_1_1379 9 77 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 77 143
  (Polychromatic418967fa.accept_18_8_5_17_1_1388 8 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 77 143 (accept_3_2 7 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 77
  143 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 77 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 77 143 (Polychromatic418967fa.accept_10_5_7_3_1_561 5 77 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 77 143 (accept_3_2 4 77 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 77 143 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 77 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 77 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 77
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 143 (accept_3_2 1 77 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 77
  143))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 76 143 (Eq.refl Bool.true)
  (allA_of_3_0 68 76 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 69 75 143 (Eq.refl Bool.true)
  (allA_succ_of_accept 68 75 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 75 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 143 (accept_3_2 67 75 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 75 143 (Polychromatic418967fa.accept_19_9_18_10_1_7446 66 75 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 75 143
  (Polychromatic418967fa.accept_7_2_5_3_1_98 65 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 75 143 (accept_3_2 64 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  75 143 (Polychromatic418967fa.accept_22_19_9_11_1_4271 63 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 75 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 75 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 75 143 (accept_3_2 61 75 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 75 143 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 75 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 75 143
  (Polychromatic418967fa.accept_9_5_3_8_1_316 59 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 75 143 (accept_3_2 58 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  75 143 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 75 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 75 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 75 143 (accept_3_2 55 75 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 75 143 (Polychromatic418967fa.accept_14_12_5_3_1_1011 54 75 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 75 143
  (Polychromatic418967fa.accept_23_7_6_5_1_4128 53 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 75 143 (accept_3_2 52 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  75 143 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 75 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 75 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 75 143 (accept_3_2 49 75 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 75 143 (Polychromatic418967fa.accept_10_8_5_3_1_543 48 75 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 75 143
  (Polychromatic418967fa.accept_9_2_3_8_1_318 47 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 75 143 (accept_3_2 46 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  75 143 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 75 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 75 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 143 (accept_3_2 43 75 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 75 143 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 75 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 75 143
  (Polychromatic418967fa.accept_9_5_3_8_1_316 41 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 75 143 (accept_3_2 40 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  75 143 (Polychromatic418967fa.accept_16_7_11_15_1_2929 39 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 75 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 75 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 143 (accept_3_2 37 75 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 75 143 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 75 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 75 143
  (Polychromatic418967fa.accept_16_3_11_15_1_1963 35 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 75 143 (accept_3_2 34 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  75 143 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 75 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 75 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 143 (accept_3_2 31 75 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 75 143 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 75 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 75 143
  (Polychromatic418967fa.accept_7_1_5_3_1_268 29 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 75 143 (accept_3_2 28 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  75 143 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 75 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 75 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 143 (accept_3_2 25 75 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 75 143 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 75 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 75 143
  (Polychromatic418967fa.accept_7_2_5_3_1_98 23 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 75 143 (accept_3_2 22 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  75 143 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 75 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 75 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 143 (accept_3_2 19 75 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 143 (Polychromatic418967fa.accept_10_8_5_3_1_543 18 75 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 143
  (Polychromatic418967fa.accept_10_7_5_3_1_542 17 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 75 143 (accept_3_2 16 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  75 143 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 75 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 75 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 143 (accept_3_2 13 75 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 75 143 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 75 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 143
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 75 143 (accept_3_2 10 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  75 143 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 75 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 75 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 143 (accept_3_2 7 75 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 143 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 75 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 75 143
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 75 143 (accept_3_2 4 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 75
  143 (Polychromatic418967fa.accept_16_3_11_15_1_1963 3 75 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 75 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 75 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 143 (accept_3_2 1 75 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 75 143))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  70 74 143 (Eq.refl Bool.true) (allA_succ_of_accept 69 74 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 74 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 74 143
  (Polychromatic418967fa.accept_9_5_2_8_1_109 68 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 74 143 (accept_3_2 67 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  74 143 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 74 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 74 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 74 143 (accept_3_2 64 74 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 74 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 74 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 74 143
  (Polychromatic418967fa.accept_7_6_4_3_1_266 62 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 74 143 (accept_3_2 61 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  74 143 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 74 143 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 74 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 74 143 (accept_3_2 58 74 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 74 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 74 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 74 143
  (Polychromatic418967fa.accept_12_8_2_11_1_246 56 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 74 143 (accept_3_2 55 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  74 143 (Polychromatic418967fa.accept_15_9_14_8_1_1396 54 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 74 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 74 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 74 143 (accept_3_2 52 74 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 74 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 74 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 74 143
  (Polychromatic418967fa.accept_7_1_4_3_1_21 50 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 74 143 (accept_3_2 49 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  74 143 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 74 143 (Polychromatic418967fa.accept_10_7_4_3_1_560 47 74 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 74 143 (accept_3_2 46 74 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 74 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 74 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 74 143
  (Polychromatic418967fa.accept_12_8_2_11_1_246 44 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 74 143 (accept_3_2 43 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  74 143 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 74 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 74 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 74 143 (accept_3_2 40 74 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 74 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 74 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 74 143
  (Polychromatic418967fa.accept_26_12_22_13_1_7445 38 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 74 143 (accept_3_2 37 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 74 143 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 74 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 74 143 (Polychromatic418967fa.accept_14_7_4_3_1_488 35 74 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 74 143 (accept_3_2 34 74 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 74 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 33
  74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 74 143
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 74 143 (accept_3_2 31 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  74 143 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 74 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 74 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 74 143 (accept_3_2 28 74 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 74 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 74 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 74 143
  (Polychromatic418967fa.accept_18_8_2_17_1_4782 26 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 74 143 (accept_3_2 25 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  74 143 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 74 143 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 74 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 74 143 (accept_3_2 22 74 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 74 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 74 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 74 143
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 74 143 (accept_3_2 19 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  74 143 (Polychromatic418967fa.accept_19_18_17_10_1_7444 18 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 74 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 74 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 74 143 (accept_3_2 16 74 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 74 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 74 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 74 143
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 74 143 (accept_3_2 13 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  74 143 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 74 143 (Polychromatic418967fa.accept_16_11_10_15_1_6301 11 74 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 74 143 (accept_3_2 10 74 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 74 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 74 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 74 143
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 74 143 (accept_3_2 7 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 74
  143 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 74 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 74 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 74 143 (accept_3_2 4 74 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 74 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 74 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 74 143 (Polychromatic418967fa.accept_19_2_17_10_1_4629
  2 74 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 143 (accept_3_2 1 74
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  143)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 73 143 (Eq.refl Bool.true)
  (allA_of_3_0 71 73 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 72 143 (allA_succ_of_accept 71 72 143
  (Polychromatic418967fa.accept_7_1_2_3_1_257 71 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 72 143 (accept_3_2 70 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  72 143 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 72 143 (Polychromatic418967fa.accept_7_5_2_3_1_106 68 72 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 72 143 (accept_3_2 67 72 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 72 143 (Polychromatic418967fa.accept_19_9_15_10_1_7443 66 72 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 72 143
  (Polychromatic418967fa.accept_10_5_2_3_1_239 65 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 72 143 (accept_3_2 64 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  72 143 (Polychromatic418967fa.accept_15_3_12_8_1_738 63 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 72 143 (Polychromatic418967fa.accept_7_6_2_3_1_107 62 72 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 143 (accept_3_2 61 72 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 72 143 (Polychromatic418967fa.accept_16_12_8_15_1_5119 60 72 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 72 143
  (Polychromatic418967fa.accept_17_8_4_7_1_7442 59 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 72 143 (accept_3_2 58 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  72 143 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 72 143 (Polychromatic418967fa.accept_15_11_12_8_1_739 56 72 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 143 (accept_3_2 55 72 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 72 143 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 72 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 72 143
  (Polychromatic418967fa.accept_20_13_12_3_1_5972 53 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 72 143 (accept_3_2 52 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  72 143 (Polychromatic418967fa.accept_10_1_2_3_1_1910 51 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 72 143 (Polychromatic418967fa.accept_7_1_2_3_1_257 50 72 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 72 143 (accept_3_2 49 72 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 72 143 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 72 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 72 143
  (Polychromatic418967fa.accept_7_5_2_3_1_106 47 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 72 143 (accept_3_2 46 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  72 143 (Polychromatic418967fa.accept_10_5_2_3_1_239 45 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 72 143 (Polychromatic418967fa.accept_16_12_8_15_1_5119 44 72 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 143 (accept_3_2 43 72 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 72 143 (Polychromatic418967fa.accept_17_8_4_7_1_7442 42 72 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 72 143
  (Polychromatic418967fa.accept_7_6_2_3_1_107 41 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 72 143 (accept_3_2 40 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  72 143 (Polychromatic418967fa.accept_16_7_8_15_1_6327 39 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 72 143 (Polychromatic418967fa.accept_22_16_6_11_1_7441 38 72 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 143 (accept_3_2 37 72 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 72 143 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 72 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 72 143
  (Polychromatic418967fa.accept_10_5_2_3_1_239 35 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 72 143 (accept_3_2 34 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  72 143 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 72 143 (Polychromatic418967fa.accept_26_6_20_13_1_7440 32 72 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 72 143 (accept_3_2 31 72 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 72 143 (Polychromatic418967fa.accept_19_11_15_10_1_7406 30 72
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 72 143
  (Polychromatic418967fa.accept_7_1_2_3_1_257 29 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 72 143 (accept_3_2 28 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  72 143 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 72 143 (Polychromatic418967fa.accept_7_5_2_3_1_106 26 72 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 143 (accept_3_2 25 72 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 72 143 (Polychromatic418967fa.accept_19_5_15_10_1_7405 24 72 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 72 143
  (Polychromatic418967fa.accept_16_7_8_15_1_6327 23 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 72 143 (accept_3_2 22 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  72 143 (Polychromatic418967fa.accept_10_1_2_3_1_1910 21 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 72 143 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 72 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 143 (accept_3_2 19 72 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 72 143 (Polychromatic418967fa.accept_15_3_12_8_1_738 18 72 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 72 143
  (Polychromatic418967fa.accept_16_1_8_15_1_1945 17 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 72 143 (accept_3_2 16 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  72 143 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 72 143 (Polychromatic418967fa.accept_17_14_4_7_1_7439 14 72 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 143 (accept_3_2 13 72 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 72 143 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 72 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 72 143
  (Polychromatic418967fa.accept_10_1_2_3_1_1910 11 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 72 143 (accept_3_2 10 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  72 143 (Polychromatic418967fa.accept_16_9_8_15_1_5095 9 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 72 143 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 72 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 143 (accept_3_2 7 72 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 72 143 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 72 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 72 143
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 72 143 (accept_3_2 4 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 72
  143 (Polychromatic418967fa.accept_15_3_12_8_1_738 3 72 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 72 143 (Polychromatic418967fa.accept_21_2_9_17_1_4376 2 72 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 143 (accept_3_2 1 72 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 72 143))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 71 143 (allA_succ_of_accept 70 71 143 (accept_3_2 70 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 71 143 (Polychromatic418967fa.accept_19_12_14_10_1_4625 69 71 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 71 143 (Polychromatic418967fa.accept_7_5_1_3_1_103 68 71 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 143 (accept_3_2 67 71 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 143 (Polychromatic418967fa.accept_21_3_8_17_1_7438
  66 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 143
  (Polychromatic418967fa.accept_7_2_1_3_1_102 65 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 143 (accept_3_2 64 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 143 (Polychromatic418967fa.accept_15_3_11_8_1_4186 63 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 143 (Polychromatic418967fa.accept_10_2_1_3_1_233 62 71 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 143 (accept_3_2 61 71 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 143 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 71 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 143
  (Polychromatic418967fa.accept_16_11_7_15_1_1998 59 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 143 (accept_3_2 58 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 143 (Polychromatic418967fa.accept_15_12_11_8_1_1392 57 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 143 (Polychromatic418967fa.accept_16_8_7_15_1_6339 56 71 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 143 (accept_3_2 55 71 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 143 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 71 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 143
  (Polychromatic418967fa.accept_7_4_1_3_1_277 53 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 143 (accept_3_2 52 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 143 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 143 (Polychromatic418967fa.accept_15_5_11_8_1_1391 50 71 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 143 (accept_3_2 49 71 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 143 (Polychromatic418967fa.accept_10_8_1_3_1_1374 48 71 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 143
  (Polychromatic418967fa.accept_7_5_1_3_1_103 47 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 143 (accept_3_2 46 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 143 (Polychromatic418967fa.accept_19_7_14_10_1_6034 45 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 143 (Polychromatic418967fa.accept_7_2_1_3_1_102 44 71 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 143 (accept_3_2 43 71 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 143 (Polychromatic418967fa.accept_10_2_1_3_1_233 42 71 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 143
  (Polychromatic418967fa.accept_21_20_8_17_1_7437 41 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 143 (accept_3_2 40 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 143 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 143 (Polychromatic418967fa.accept_10_8_1_3_1_1374 38 71 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 143 (accept_3_2 37 71 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 143 (Polychromatic418967fa.accept_21_15_8_17_1_7436 36 71 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 143
  (Polychromatic418967fa.accept_15_5_11_8_1_1391 35 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 143 (accept_3_2 34 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 143 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 143 (Polychromatic418967fa.accept_7_4_1_3_1_277 32 71 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 143 (accept_3_2 31 71 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 143 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 71 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 143
  (Polychromatic418967fa.accept_17_12_3_7_1_7410 29 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 143 (accept_3_2 28 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 143 (Polychromatic418967fa.accept_15_12_11_8_1_1392 27 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 143 (Polychromatic418967fa.accept_7_5_1_3_1_103 26 71 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 143 (accept_3_2 25 71 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 143 (Polychromatic418967fa.accept_16_8_7_15_1_6339 24 71 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 143
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 143 (accept_3_2 22 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 143 (Polychromatic418967fa.accept_17_4_3_7_1_4971 21 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 143 (Polychromatic418967fa.accept_15_5_11_8_1_1391 20 71 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 143 (accept_3_2 19 71 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 143 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 71 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 143
  (Polychromatic418967fa.accept_22_17_5_11_1_2772 17 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 143 (accept_3_2 16 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 143 (Polychromatic418967fa.accept_19_15_14_10_1_4667 15 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 143 (Polychromatic418967fa.accept_16_14_7_15_1_3947 14 71 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 143 (accept_3_2 13 71 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 143 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 71 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 143
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 143 (accept_3_2 10 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 143 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 143 (Polychromatic418967fa.accept_10_8_1_3_1_1374 8 71 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 143 (accept_3_2 7 71 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 143 (Polychromatic418967fa.accept_16_6_7_15_1_1942 6 71 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 143
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 143 (accept_3_2 4 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  143 (Polychromatic418967fa.accept_15_3_11_8_1_4186 3 71 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 71 143 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 71 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 143 (accept_3_2 1 71 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 71 143)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 70 143 (allA_of_3_0 70 70 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 69 143
  (allA_succ_of_accept 68 69 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 69 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 69 143 (accept_3_2 67 69 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 69 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 69 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 69 143 (Polychromatic418967fa.accept_7_2_6_3_1_100 65
  69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 143 (accept_3_2 64 69
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 143
  (Polychromatic418967fa.accept_12_3_9_11_1_231 63 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 69 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 69 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 143 (accept_3_2 61 69 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 69 143 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 69 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 69 143 (Polychromatic418967fa.accept_9_5_6_8_1_101 59
  69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 143 (accept_3_2 58 69
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 143
  (Polychromatic418967fa.accept_9_3_6_8_1_308 57 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 69 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 69 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 69 143 (accept_3_2 55 69 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 69 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 69 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 69 143 (Polychromatic418967fa.accept_7_4_6_3_1_271 53
  69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 143 (accept_3_2 52 69
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 143
  (Polychromatic418967fa.accept_7_2_6_3_1_100 51 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 69 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 69 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 143 (accept_3_2 49 69 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 69 143 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 69 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 69 143 (Polychromatic418967fa.accept_9_2_6_8_1_321 47
  69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 143 (accept_3_2 46 69
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 143
  (Polychromatic418967fa.accept_17_11_1_7_1_2657 45 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 69 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 69 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 143 (accept_3_2 43 69 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 69 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 69 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 69 143 (Polychromatic418967fa.accept_9_5_6_8_1_101 41
  69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 143 (accept_3_2 40 69
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 143
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 69 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 69 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 69 143 (accept_3_2 37 69 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 69 143 (Polychromatic418967fa.accept_10_6_9_3_1_935 36 69 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 69 143 (Polychromatic418967fa.accept_20_15_9_3_1_7435
  35 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 143 (accept_3_2 34
  69 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 143
  (Polychromatic418967fa.accept_15_3_9_8_1_3164 33 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 69 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 69 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 143 (accept_3_2 31 69 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 69 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 69 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 143 (Polychromatic418967fa.accept_9_2_6_8_1_321 29
  69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 143 (accept_3_2 28 69
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 143
  (Polychromatic418967fa.accept_12_3_9_11_1_231 27 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 69 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 69 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 143 (accept_3_2 25 69 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 69 143 (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 69 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 143 (Polychromatic418967fa.accept_7_2_6_3_1_100 23
  69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 143 (accept_3_2 22 69
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 143
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 69 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 69 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 143 (accept_3_2 19 69 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 69 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 69 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 143 (Polychromatic418967fa.accept_15_2_9_8_1_736
  17 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 143 (accept_3_2 16
  69 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 143
  (Polychromatic418967fa.accept_12_3_9_11_1_231 15 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 69 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 69 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 143 (accept_3_2 13 69 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 69 143 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 69 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 143 (Polychromatic418967fa.accept_7_4_6_3_1_271 11
  69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 143 (accept_3_2 10 69
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 143 (Polychromatic418967fa.accept_7_2_6_3_1_100
  9 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 143 (accept_3_2 7 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69
  143 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 69 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 143 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 69 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 143 (accept_3_2 4 69 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 69 143 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 69 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 69
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 143 (accept_3_2 1 69 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  143))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 143 (allA_succ_of_accept 67 68
  143 (accept_3_2 67 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 68 143
  (Polychromatic418967fa.accept_9_3_5_8_1_99 66 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 68 143 (Polychromatic418967fa.accept_7_2_5_3_1_98 65 68 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 68 143 (accept_3_2 64 68 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 68 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 68 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 68 143 (Polychromatic418967fa.accept_12_2_8_11_1_31
  62 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 68 143 (accept_3_2 61
  68 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 68 143
  (Polychromatic418967fa.accept_9_6_5_8_1_598 60 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 68 143 (Polychromatic418967fa.accept_8_3_4_7_1_475 59 68 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 68 143 (accept_3_2 58 68 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 68 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 68 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 68 143 (Polychromatic418967fa.accept_9_2_5_8_1_11 56
  68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 68 143 (accept_3_2 55 68
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 68 143
  (Polychromatic418967fa.accept_20_14_8_3_1_6011 54 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 68 143 (Polychromatic418967fa.accept_16_5_4_15_1_1102 53 68 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 68 143 (accept_3_2 52 68 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 68 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 68 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 68 143 (Polychromatic418967fa.accept_7_1_5_3_1_268 50
  68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 68 143 (accept_3_2 49 68
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 68 143 (Polychromatic418967fa.accept_9_3_5_8_1_99
  48 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 68 143
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 68 143 (accept_3_2 46 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  68 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 68 143 (Polychromatic418967fa.accept_7_2_5_3_1_98 44 68 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 68 143 (accept_3_2 43 68 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 68 143 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 68 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 68 143
  (Polychromatic418967fa.accept_10_1_8_3_1_947 41 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 68 143 (accept_3_2 40 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  68 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 68 143 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 68 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 68 143 (accept_3_2 37 68 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 68 143 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 68 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 68 143
  (Polychromatic418967fa.accept_8_3_4_7_1_475 35 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 68 143 (accept_3_2 34 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  68 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 68 143 (Polychromatic418967fa.accept_21_11_5_17_1_760 32 68 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 68 143 (accept_3_2 31 68 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 68 143 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 68 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 68 143
  (Polychromatic418967fa.accept_7_1_5_3_1_268 29 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 68 143 (accept_3_2 28 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  68 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 68 143 (Polychromatic418967fa.accept_10_6_8_3_1_930 26 68 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 68 143 (accept_3_2 25 68 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 68 143 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 68 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 68 143
  (Polychromatic418967fa.accept_7_2_5_3_1_98 23 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 68 143 (accept_3_2 22 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  68 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 68 143 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 68 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 68 143 (accept_3_2 19 68 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 68 143 (Polychromatic418967fa.accept_19_18_11_10_1_7379 18 68 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 68 143
  (Polychromatic418967fa.accept_22_17_2_11_1_7434 17 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 68 143 (accept_3_2 16 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  68 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 68 143 (Polychromatic418967fa.accept_12_2_8_11_1_31 14 68 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 68 143 (accept_3_2 13 68 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 68 143 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 68 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 68 143
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 68 143 (accept_3_2 10 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  68 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 68 143 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 68 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 68 143 (accept_3_2 7 68 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 68 143 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 68 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 68 143
  (Polychromatic418967fa.accept_10_5_8_3_1_229 5 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 68 143 (accept_3_2 4 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 68
  143 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 68 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 68 143 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 68 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 143 (accept_3_2 1 68 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 68 143)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 143
  (allA_of_3_0 67 67 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 66 143 (allA_succ_of_accept 65 66 143
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 66 143 (accept_3_2 64 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  66 143 (Polychromatic418967fa.accept_14_7_10_3_1_1034 63 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 66 143 (Polychromatic418967fa.accept_14_6_10_3_1_1038 62 66 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 66 143 (accept_3_2 61 66 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 66 143 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 66 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 66 143
  (Polychromatic418967fa.accept_9_5_3_8_1_316 59 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 66 143 (accept_3_2 58 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  66 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 66 143 (Polychromatic418967fa.accept_9_2_3_8_1_318 56 66 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 66 143 11 5 6 13 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 66 143 (Polychromatic418967fa.accept_19_16_9_10_1_7433
  54 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 66 143
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 66 143 (accept_3_2 52 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  66 143 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 66 143 (Polychromatic418967fa.accept_9_5_3_8_1_316 50 66 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 143 (accept_3_2 49 66 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 66 143 (Polychromatic418967fa.accept_10_8_6_3_1_1394 48 66 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 66 143
  (Polychromatic418967fa.accept_9_2_3_8_1_318 47 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 66 143 (accept_3_2 46 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  66 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 66 143 11 4 6 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 66 143 (accept_3_2 43 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 66 143 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 66 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 66 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 66 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 66 143 (accept_3_2 40 66 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 66 143 (Polychromatic418967fa.accept_10_9_6_3_1_545
  39 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 66 143
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 66 143 (accept_3_2 37 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  66 143 (Polychromatic418967fa.accept_17_2_15_7_1_6213 36 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 66 143 (Polychromatic418967fa.accept_14_7_10_3_1_1034 35 66 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 66 143 (accept_3_2 34 66 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 66 143 11 3 6 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 66 143 (Polychromatic418967fa.accept_9_5_3_8_1_316 32 66 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 143 (accept_3_2 31 66 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 66 143 (Polychromatic418967fa.accept_21_9_3_17_1_4365
  30 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 66 143
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 66 143 (accept_3_2 28 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  66 143 (Polychromatic418967fa.accept_10_7_6_3_1_927 27 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 66 143 (Polychromatic418967fa.accept_17_9_15_7_1_6212 26 66 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 143 (accept_3_2 25 66 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 66 143 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 66 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 66 143
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 66 143 11 2 6 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 66 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 66 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 66 143 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 66 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 143 (accept_3_2 19 66 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 66 143 (Polychromatic418967fa.accept_10_8_6_3_1_1394
  18 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 66 143
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 66 143 (accept_3_2 16 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  66 143 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 66 143 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 66 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 143 (accept_3_2 13 66 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 66 143 (Polychromatic418967fa.accept_16_12_2_15_1_490 12 66 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 11 66 143 11 1 6 13 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 66 143 (accept_3_2 10 66 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 66 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 66 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 66 143
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 8 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 66 143 (accept_3_2 7 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 66
  143 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 66 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 66 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66 143 (accept_3_2 4 66 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 66 143 (Polychromatic418967fa.accept_16_3_2_15_1_7367 3 66 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 66 143 (Polychromatic418967fa.accept_9_2_3_8_1_318 2
  66 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 143 (accept_3_2 1 66 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  143)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 143 (allA_succ_of_accept 64 65 143
  (accept_3_2 64 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 65 143
  (Polychromatic418967fa.accept_15_3_5_8_1_1387 63 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 65 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 65 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 143 (accept_3_2 61 65 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 65 143 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 65 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 143 (Polychromatic418967fa.accept_9_5_2_8_1_109 59
  65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 65 143 (accept_3_2 58 65
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 65 143
  (Polychromatic418967fa.accept_7_1_2_3_1_257 57 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 65 143 (Polychromatic418967fa.accept_15_11_5_8_1_3157 56 65 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 143 (accept_3_2 55 65 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 65 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 65 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 143 (Polychromatic418967fa.accept_16_5_1_15_1_3922
  53 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 65 143 13 4 5 11 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 65 143
  (Polychromatic418967fa.accept_9_6_2_8_1_592 51 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 65 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 65 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 143 (accept_3_2 49 65 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 65 143 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 65 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 143 (Polychromatic418967fa.accept_7_5_2_3_1_106 47
  65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 65 143 (accept_3_2 46 65
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 65 143
  (Polychromatic418967fa.accept_21_3_2_17_1_7432 45 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 65 143 (Polychromatic418967fa.accept_15_14_5_8_1_3175 44 65 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 143 (accept_3_2 43 65 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 65 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 65 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 143 (Polychromatic418967fa.accept_7_6_2_3_1_107 41
  65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 65 143 (accept_3_2 40 65
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 65 143 13 3 5 11 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 65 143
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 65 143 (accept_3_2 37 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  65 143 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 65 143 (Polychromatic418967fa.accept_19_16_8_10_1_7431 35 65 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 65 143 (accept_3_2 34 65 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 65 143 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 65 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 65 143
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 65 143 (accept_3_2 31 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  65 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 65 143 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 65 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 65 143 (accept_3_2 28 65 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 65 143 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 65 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 65 143 13 2 5 11 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 65 143 (accept_3_2 25 65 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 143 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 65 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 143
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 143 (accept_3_2 22 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 143 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 143 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 65 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 143 (accept_3_2 19 65 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 65 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 143
  (Polychromatic418967fa.accept_10_7_5_3_1_542 17 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 143 (accept_3_2 16 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 143 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 65 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13 65 143 13 1 5 11 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12 65 143 (Polychromatic418967fa.accept_7_5_2_3_1_106 12
  65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 143
  (Polychromatic418967fa.accept_15_11_5_8_1_3157 11 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 143 (accept_3_2 10 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 143 (Polychromatic418967fa.accept_21_9_2_17_1_7394 9 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 143 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 65 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 143 (accept_3_2 7 65 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 65 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 143
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 143 (accept_3_2 4 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  143 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 65 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 65 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 143 (accept_3_2 1 65 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 143))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 143
  (allA_of_3_0 64 64 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 63 143 (allA_succ_of_accept 62 63 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 143 (accept_3_2 61 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  63 143 (Polychromatic418967fa.accept_14_4_7_3_1_1718 60 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 63 143 (Polychromatic418967fa.accept_19_2_6_10_1_3364 59 63 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 143 (accept_3_2 58 63 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 143 (Polychromatic418967fa.accept_12_9_3_11_1_1097 57 63
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 63 143 (accept_3_2 55 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  63 143 (Polychromatic418967fa.accept_15_9_3_8_1_3155 54 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 63 143 (Polychromatic418967fa.accept_14_11_7_3_1_3416 53 63 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 143 (accept_3_2 52 63 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 143 (Polychromatic418967fa.accept_18_15_9_17_1_6043 51 63
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 143 (accept_3_2 49 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  63 143 (Polychromatic418967fa.accept_18_12_9_17_1_7428 48 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 63 143 (Polychromatic418967fa.accept_19_9_6_10_1_7430 47 63 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 143 (accept_3_2 46 63 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 143 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 63
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 143 (accept_3_2 43 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  63 143 (Polychromatic418967fa.accept_15_12_3_8_1_5245 42 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 63 143 (Polychromatic418967fa.accept_15_11_3_8_1_750 41 63 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 143 (accept_3_2 40 63 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 143 (Polychromatic418967fa.accept_14_11_7_3_1_3416 39 63 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 143 (accept_3_2 37 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  63 143 (Polychromatic418967fa.accept_17_2_12_7_1_7429 36 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 63 143 (Polychromatic418967fa.accept_15_5_3_8_1_748 35 63 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 143 (accept_3_2 34 63 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 143 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 63 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 143 (accept_3_2 31 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  63 143 (Polychromatic418967fa.accept_18_12_9_17_1_7428 30 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 63 143 (Polychromatic418967fa.accept_24_5_15_23_1_5647 29 63 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 143 (accept_3_2 28 63 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 143 (Polychromatic418967fa.accept_15_12_3_8_1_5245 27 63
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 143 (accept_3_2 25 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  63 143 (Polychromatic418967fa.accept_14_10_7_3_1_1022 24 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 63 143 (Polychromatic418967fa.accept_19_4_6_10_1_7396 23 63 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 143 (accept_3_2 22 63 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 143 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 63
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 143 (accept_3_2 19 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  63 143 (Polychromatic418967fa.accept_14_4_7_3_1_1718 18 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 63 143 (Polychromatic418967fa.accept_25_17_13_18_1_7427 17 63 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 143 (accept_3_2 16 63 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 143 (Polychromatic418967fa.accept_18_15_9_17_1_6043 15 63
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 143 (accept_3_2 13 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  63 143 (Polychromatic418967fa.accept_15_12_3_8_1_5245 12 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 63 143 (Polychromatic418967fa.accept_14_11_7_3_1_3416 11 63 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 143 (accept_3_2 10 63 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 143 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 63 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 143 (accept_3_2 7 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63
  143 (Polychromatic418967fa.accept_25_6_13_18_1_7426 6 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 63 143 (Polychromatic418967fa.accept_15_5_3_8_1_748 5 63 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 143 (accept_3_2 4 63 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 143 (Polychromatic418967fa.accept_17_3_12_7_1_4949 3 63 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 63 143 (accept_3_2 1 63 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  143))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 143 (allA_succ_of_accept 61 62 143
  (accept_3_2 61 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 62 143
  (Polychromatic418967fa.accept_7_4_6_3_1_271 60 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 62 143 (Polychromatic418967fa.accept_18_5_8_17_1_3478 59 62 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 62 143 (accept_3_2 58 62 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 62 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 62 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 62 143 (Polychromatic418967fa.accept_12_8_2_11_1_246
  56 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 62 143 (accept_3_2 55
  62 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 62 143
  (Polychromatic418967fa.accept_15_9_2_8_1_1379 54 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 62 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 62 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 62 143 (accept_3_2 52 62 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 62 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 62 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 62 143 (Polychromatic418967fa.accept_20_10_2_3_1_7425
  50 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 62 143 (accept_3_2 49
  62 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 62 143
  (Polychromatic418967fa.accept_22_4_18_11_1_5898 48 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 62 143 (Polychromatic418967fa.accept_17_13_11_7_1_4961 47 62 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 62 143 (accept_3_2 46 62 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 62 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 62 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 62 143 (Polychromatic418967fa.accept_7_2_6_3_1_100 44
  62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 62 143 (accept_3_2 43 62
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 62 143
  (Polychromatic418967fa.accept_16_10_14_15_1_2933 42 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 62 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 62 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 62 143 (accept_3_2 40 62 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 62 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 62 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 62 143
  (Polychromatic418967fa.accept_14_10_6_3_1_1055 38 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 62 143 (accept_3_2 37 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  62 143 (Polychromatic418967fa.accept_15_6_2_8_1_2223 36 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 62 143 (Polychromatic418967fa.accept_10_5_2_3_1_239 35 62 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 62 143 (accept_3_2 34 62 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 62 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 62 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 62 143
  (Polychromatic418967fa.accept_7_4_6_3_1_271 32 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 62 143 (accept_3_2 31 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  62 143 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 62 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 62 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 62 143 (accept_3_2 28 62 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 62 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 62 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 62 143
  (Polychromatic418967fa.accept_16_10_14_15_1_2933 26 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 62 143 (accept_3_2 25 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 62 143 (Polychromatic418967fa.accept_14_10_6_3_1_1055 24 62 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 62 143 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 62 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 62 143 (accept_3_2 22 62 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 62 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 21
  62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 62 143
  (Polychromatic418967fa.accept_12_8_2_11_1_246 20 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 62 143 (accept_3_2 19 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  62 143 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 62 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 62 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 62 143 (accept_3_2 16 62 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 62 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 62 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 62 143
  (Polychromatic418967fa.accept_19_14_5_10_1_4610 14 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 62 143 (accept_3_2 13 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  62 143 (Polychromatic418967fa.accept_22_12_18_11_1_7424 12 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 62 143 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 62 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 62 143 (accept_3_2 10 62 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 62 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 62 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 62 143
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 62 143 (accept_3_2 7 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 62
  143 (Polychromatic418967fa.accept_15_6_2_8_1_2223 6 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 62 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 62 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 62 143 (accept_3_2 4 62 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 62 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 62 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 62 143
  (Polychromatic418967fa.accept_7_2_6_3_1_100 2 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 62 143 (accept_3_2 1 62 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  143)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 143 (allA_of_3_0 61 61 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 60 143 (allA_succ_of_accept 59 60 143
  (Polychromatic418967fa.accept_8_3_4_7_1_475 59 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 60 143 (accept_3_2 58 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  60 143 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 60 143 (Polychromatic418967fa.accept_9_2_6_8_1_321 56 60 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 60 143 (accept_3_2 55 60 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 60 143 (Polychromatic418967fa.accept_23_8_14_5_1_7423 54 60 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 60 143
  (Polychromatic418967fa.accept_17_2_9_7_1_5002 53 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 60 143 (accept_3_2 52 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  60 143 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 60 143 (Polychromatic418967fa.accept_7_1_4_3_1_21 50 60 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 60 143 (accept_3_2 49 60 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 60 143 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 60 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 60 143
  (Polychromatic418967fa.accept_9_2_6_8_1_321 47 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 60 143 (accept_3_2 46 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  60 143 (Polychromatic418967fa.accept_16_13_12_15_1_6290 45 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 60 143 (Polychromatic418967fa.accept_24_20_12_23_1_7422 44 60 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 143 (accept_3_2 43 60 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 60 143 (Polychromatic418967fa.accept_22_20_16_11_1_7421 42 60
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 60 143
  (Polychromatic418967fa.accept_7_6_4_3_1_266 41 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 60 143 (accept_3_2 40 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  60 143 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 60 143 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 60 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 143 (accept_3_2 37 60 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 60 143 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 60 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 60 143
  (Polychromatic418967fa.accept_8_3_4_7_1_475 35 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 60 143 (accept_3_2 34 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  60 143 (Polychromatic418967fa.accept_18_15_6_17_1_2386 33 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 60 143 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 60 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 143 (accept_3_2 31 60 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 60 143 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 60 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 60 143
  (Polychromatic418967fa.accept_7_1_4_3_1_21 29 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 60 143 (accept_3_2 28 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  60 143 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 60 143 (Polychromatic418967fa.accept_19_7_3_10_1_4674 26 60 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 60 143 (accept_3_2 25 60 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 60 143 (Polychromatic418967fa.accept_16_8_12_15_1_2005 24 60
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 60 143
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 60 143 (accept_3_2 22 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  60 143 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 60 143 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 60 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 143 (accept_3_2 19 60 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 60 143 (Polychromatic418967fa.accept_16_2_12_15_1_2908 18 60 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 60 143
  (Polychromatic418967fa.accept_22_17_16_11_1_7420 17 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 60 143 (accept_3_2 16 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 60 143 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 60 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 60 143 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 60 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 143 (accept_3_2 13 60 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 60 143 (Polychromatic418967fa.accept_9_3_6_8_1_308 12
  60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 60 143
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 60 143 (accept_3_2 10 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  60 143 (Polychromatic418967fa.accept_19_9_3_10_1_6017 9 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 60 143 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 60 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 143 (accept_3_2 7 60 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 60 143 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 60 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 60 143
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 60 143 (accept_3_2 4 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 60
  143 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 60 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 60 143 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 60 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 143 (accept_3_2 1 60 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 60 143)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 143
  (allA_succ_of_accept 58 59 143 (accept_3_2 58 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  59 143 (Polychromatic418967fa.accept_9_3_5_8_1_99 57 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 59 143 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 59 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 143 (accept_3_2 55 59 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 59 143 (Polychromatic418967fa.accept_10_4_9_3_1_1907 54 59 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 143
  (Polychromatic418967fa.accept_24_5_11_23_1_7419 53 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 143 (accept_3_2 52 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 143 (Polychromatic418967fa.accept_9_6_5_8_1_598 51 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 143 (Polychromatic418967fa.accept_15_5_14_8_1_1376 50 59 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 143 (accept_3_2 49 59 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 143 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 59 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 143
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 143 (accept_3_2 46 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 143 (Polychromatic418967fa.accept_22_1_15_11_1_7418 45 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 143 (Polychromatic418967fa.accept_8_4_3_7_1_491 44 59 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 143 (accept_3_2 43 59 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 143 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 59 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 143
  (Polychromatic418967fa.accept_23_18_13_5_1_7417 41 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 143 (accept_3_2 40 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 143 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 143 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 59 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 143 (accept_3_2 37 59 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 143 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 59 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 143
  (Polychromatic418967fa.accept_15_5_14_8_1_1376 35 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 143 (accept_3_2 34 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 143 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 143 (Polychromatic418967fa.accept_19_13_2_10_1_7416 32 59 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 143 (accept_3_2 31 59 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 143 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 59 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 143
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 143 (accept_3_2 28 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 143 (Polychromatic418967fa.accept_19_8_2_10_1_7415 27 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 143 (Polychromatic418967fa.accept_10_6_9_3_1_935 26 59 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 143 (accept_3_2 25 59 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 143 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 59 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 143
  (Polychromatic418967fa.accept_16_7_11_15_1_2929 23 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 143 (accept_3_2 22 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 143 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 143 (Polychromatic418967fa.accept_8_4_3_7_1_491 20 59 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 143 (accept_3_2 19 59 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 143 (Polychromatic418967fa.accept_17_1_8_7_1_4982 18 59 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 143
  (Polychromatic418967fa.accept_16_1_11_15_1_498 17 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 143 (accept_3_2 16 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 143 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 143 (Polychromatic418967fa.accept_10_4_9_3_1_1907 14 59 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 143 (accept_3_2 13 59 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 143 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 59 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 143
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 143 (accept_3_2 10 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 143 (Polychromatic418967fa.accept_15_9_14_8_1_1396 9 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 143 (Polychromatic418967fa.accept_18_8_5_17_1_1388 8 59 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 143 (accept_3_2 7 59 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 143 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 59 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 143
  (Polychromatic418967fa.accept_15_5_14_8_1_1376 5 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 143 (accept_3_2 4 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  143 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 59 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 59 143 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 59 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 143 (accept_3_2 1 59 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 59 143))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 143 (allA_of_3_0
  58 58 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 57 143 (allA_succ_of_accept 56 57 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 143 (accept_3_2 55 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  57 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 57 143 (Polychromatic418967fa.accept_7_4_1_3_1_277 53 57 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 143 (accept_3_2 52 57 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 143 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 57 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 143
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 143 (accept_3_2 49 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  57 143 (Polychromatic418967fa.accept_15_3_12_8_1_738 48 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 57 143 (Polychromatic418967fa.accept_7_5_1_3_1_103 47 57 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 143 (accept_3_2 46 57 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 143 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 57 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 143 (accept_3_2 43 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  57 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 57 143 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 57 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 143 (accept_3_2 40 57 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 143 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 57 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 143
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 143 (accept_3_2 37 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  57 143 (Polychromatic418967fa.accept_10_6_7_3_1_547 36 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 57 143 (Polychromatic418967fa.accept_10_5_7_3_1_561 35 57 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 143 (accept_3_2 34 57 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 143 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 57 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 143 (accept_3_2 31 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  57 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 57 143 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 57 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 143 (accept_3_2 28 57 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 143 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 57 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 143
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 143 (accept_3_2 25 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  57 143 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 57 143 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 57 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 143 (accept_3_2 22 57 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 143 (Polychromatic418967fa.accept_26_21_5_13_1_7414 21 57 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 143 (accept_3_2 19 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  57 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 57 143 (Polychromatic418967fa.accept_22_17_13_11_1_7413 17 57 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 143 (accept_3_2 16 57 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 143 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 57 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 143
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 143 (accept_3_2 13 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  57 143 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 57 143 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 57 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 143 (accept_3_2 10 57 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 143 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 57 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 143 (accept_3_2 7 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57
  143 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 57 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 143 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 57 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 143 (accept_3_2 4 57 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 143 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 57 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 57
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 143 (accept_3_2 1 57 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 143)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 143 (allA_succ_of_accept 55 56 143 (accept_3_2 55 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 56 143 (Polychromatic418967fa.accept_22_10_12_11_1_7412 54 56 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 56 143 (Polychromatic418967fa.accept_20_13_16_3_1_4479 53 56
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 143 (accept_3_2 52 56 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 56 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 51
  56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 56 143
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 56 143 (accept_3_2 49 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  56 143 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 56 143 (Polychromatic418967fa.accept_10_7_6_3_1_927 47 56 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 143 (accept_3_2 46 56 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 56 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 56 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 143
  (Polychromatic418967fa.accept_16_12_8_15_1_5119 44 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 56 143 (accept_3_2 43 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  56 143 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 56 143 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 56 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 56 143 (accept_3_2 40 56 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 56 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 56 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 143
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 38 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 56 143 (accept_3_2 37 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  56 143 (Polychromatic418967fa.accept_16_4_8_15_1_1113 36 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 56 143 (Polychromatic418967fa.accept_15_5_11_8_1_1391 35 56 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 56 143 (accept_3_2 34 56 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 56 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 56 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 56 143
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 56 143 (accept_3_2 31 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  56 143 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 56 143 (Polychromatic418967fa.accept_10_9_6_3_1_545 29 56 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 56 143 (accept_3_2 28 56 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 56 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 56 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 143
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 56 143 (accept_3_2 25 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  56 143 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 56 143 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 56 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 143 (accept_3_2 22 56 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 56 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 56 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 56 143
  (Polychromatic418967fa.accept_15_5_11_8_1_1391 20 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 56 143 (accept_3_2 19 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  56 143 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 56 143 (Polychromatic418967fa.accept_10_7_6_3_1_927 17 56 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 143 (accept_3_2 16 56 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 56 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 56 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 56 143
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 56 143 (accept_3_2 13 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  56 143 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 56 143 (Polychromatic418967fa.accept_17_11_5_7_1_6177 11 56 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 143 (accept_3_2 10 56 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 56 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 56 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 143
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 8 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 56 143 (accept_3_2 7 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 56
  143 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 56 143 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 56 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 143 (accept_3_2 4 56 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 56 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 56 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 143 (Polychromatic418967fa.accept_12_2_8_11_1_31 2
  56 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 56 143 (accept_3_2 1 56 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 143))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 55 143 (allA_of_3_0 55 55 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 54 143
  (allA_succ_of_accept 53 54 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 54 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 54 143 (accept_3_2 52 54 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 54 143 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 54 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 54 143 (Polychromatic418967fa.accept_7_1_5_3_1_268 50
  54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 143 (accept_3_2 49 54
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 143
  (Polychromatic418967fa.accept_15_3_9_8_1_3164 48 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 54 143 (Polychromatic418967fa.accept_10_7_4_3_1_560 47 54 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 54 143 (accept_3_2 46 54 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 54 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 54 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 54 143 (Polychromatic418967fa.accept_7_2_5_3_1_98 44
  54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 143 (accept_3_2 43 54
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 143
  (Polychromatic418967fa.accept_19_4_16_10_1_2171 42 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 54 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 54 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 54 143 (accept_3_2 40 54 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 54 143 (Polychromatic418967fa.accept_10_9_4_3_1_539 39 54 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 54 143 (Polychromatic418967fa.accept_17_4_3_7_1_4971
  38 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 143 (accept_3_2 37
  54 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 54 143
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 54 143 (Polychromatic418967fa.accept_25_10_4_18_1_7411 35 54 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 54 143 (accept_3_2 34 54 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 54 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 54 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 54 143 (Polychromatic418967fa.accept_15_2_9_8_1_736
  32 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 143 (accept_3_2 31
  54 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 54 143
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 54 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 54 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 54 143 (accept_3_2 28 54 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 54 143 (Polychromatic418967fa.accept_10_7_4_3_1_560 27 54 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 143
  (Polychromatic418967fa.accept_19_7_16_10_1_2172 26 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 54 143 (accept_3_2 25 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  54 143 (Polychromatic418967fa.accept_19_5_16_10_1_7384 24 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 54 143 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 54 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 54 143 (accept_3_2 22 54 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 54 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 54 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 143
  (Polychromatic418967fa.accept_19_1_16_10_1_6026 20 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 54 143 (accept_3_2 19 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  54 143 (Polychromatic418967fa.accept_15_3_9_8_1_3164 18 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 54 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 54 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 54 143 (accept_3_2 16 54 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 54 143 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 54 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 143
  (Polychromatic418967fa.accept_15_14_9_8_1_3165 14 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 54 143 (accept_3_2 13 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  54 143 (Polychromatic418967fa.accept_17_12_3_7_1_7410 12 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 54 143 (Polychromatic418967fa.accept_20_11_14_3_1_5975 11 54 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 54 143 (accept_3_2 10 54 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 54 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 54 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 143
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 54 143 (accept_3_2 7 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54
  143 (Polychromatic418967fa.accept_19_6_16_10_1_7385 6 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 54 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 54 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 143 (accept_3_2 4 54 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 54 143 (Polychromatic418967fa.accept_15_3_9_8_1_3164 3 54 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 143
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 54 143 (accept_3_2 1 54 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  143)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 143 (allA_succ_of_accept 52 53 143 (accept_3_2
  52 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 143
  (Polychromatic418967fa.accept_20_11_13_3_1_7409 51 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 53 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 143 (accept_3_2 49 53 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 143 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 53 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 143 (Polychromatic418967fa.accept_17_13_2_7_1_6122
  47 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 143 (accept_3_2 46
  53 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 143
  (Polychromatic418967fa.accept_24_21_5_23_1_7408 45 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 53 143 (Polychromatic418967fa.accept_19_6_15_10_1_2170 44 53 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 143 (accept_3_2 43 53 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 53 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 53 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 143 (Polychromatic418967fa.accept_7_6_4_3_1_266 41
  53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 53 143 (accept_3_2 40 53
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 53 143
  (Polychromatic418967fa.accept_22_17_9_11_1_7407 39 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 53 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 53 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 143 (accept_3_2 37 53 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 53 143 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 53 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 143 (Polychromatic418967fa.accept_14_7_11_3_1_5365
  35 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 53 143 (accept_3_2 34
  53 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 53 143
  (Polychromatic418967fa.accept_16_1_5_15_1_2918 33 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 53 143 (Polychromatic418967fa.accept_17_15_2_7_1_7389 32 53 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 143 (accept_3_2 31 53 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 53 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 53 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 143 (Polychromatic418967fa.accept_7_1_4_3_1_21 29
  53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 53 143 (accept_3_2 28 53
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 53 143
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 53 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 53 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 143 (accept_3_2 25 53 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 53 143 (Polychromatic418967fa.accept_19_5_15_10_1_7405 24 53 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 143
  (Polychromatic418967fa.accept_19_4_15_10_1_4602 23 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 143 (accept_3_2 22 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 143 (Polychromatic418967fa.accept_14_7_11_3_1_5365 21 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 143 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 53 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 143 (accept_3_2 19 53 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 53 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 143
  (Polychromatic418967fa.accept_16_1_5_15_1_2918 17 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 143 (accept_3_2 16 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 143 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 53 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 143 (accept_3_2 13 53 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 143 (Polychromatic418967fa.accept_17_12_2_7_1_3813 12 53 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 143
  (Polychromatic418967fa.accept_19_11_15_10_1_7406 11 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 53 143 (accept_3_2 10 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 53 143 (Polychromatic418967fa.accept_17_9_2_7_1_2689 9 53 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 53 143 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 53 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 143 (accept_3_2 7 53 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 53
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 143
  (Polychromatic418967fa.accept_19_5_15_10_1_7405 5 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 143 (accept_3_2 4 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  143 (Polychromatic418967fa.accept_19_3_15_10_1_4688 3 53 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 53 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 53 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 143 (accept_3_2 1 53 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 53 143))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 143
  (allA_of_3_0 52 52 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 143 (allA_succ_of_accept 50 51 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 143 (accept_3_2 49 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  51 143 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 51 143 (Polychromatic418967fa.accept_7_5_2_3_1_106 47 51 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 143 (accept_3_2 46 51 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 143 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 51 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 143 (accept_3_2 43 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  51 143 (Polychromatic418967fa.accept_10_2_1_3_1_233 42 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 51 143 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 51 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 143 (accept_3_2 40 51 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 143 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 51 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 143 (accept_3_2 37 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  51 143 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 51 143 (Polychromatic418967fa.accept_19_16_13_10_1_6025 35 51 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 143 (accept_3_2 34 51 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 143 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 51 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 143 (accept_3_2 31 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  51 143 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 51 143 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 51 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 143 (accept_3_2 28 51 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 143 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 51 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 143 (accept_3_2 25 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  51 143 (Polychromatic418967fa.accept_18_6_15_17_1_7363 24 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 51 143 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 51 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 143 (accept_3_2 22 51 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 143 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 51 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 143 (accept_3_2 19 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  51 143 (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 51 143 (Polychromatic418967fa.accept_15_2_6_8_1_754 17 51 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 143 (accept_3_2 16 51 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 143 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 51 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 143 (accept_3_2 13 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  51 143 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 51 143 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 51 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 143 (accept_3_2 10 51 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 143 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 51 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 143 (accept_3_2 7 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51
  143 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 51 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 143 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 51 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 143 (accept_3_2 4 51 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 51 143 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 51 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 51
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 143 (accept_3_2 1 51 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 143)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 143 (allA_succ_of_accept 49 50 143 (accept_3_2 49 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 50 143 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 50 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 50 143 (Polychromatic418967fa.accept_7_5_1_3_1_103 47 50 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 143 (accept_3_2 46 50 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 50 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 45
  50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 50 143
  (Polychromatic418967fa.accept_7_2_1_3_1_102 44 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 50 143 (accept_3_2 43 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  50 143 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 50 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 50 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 50 143 (accept_3_2 40 50 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 50 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 50 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 143
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 50 143 (accept_3_2 37 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  50 143 (Polychromatic418967fa.accept_19_17_12_10_1_7404 36 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 50 143 (Polychromatic418967fa.accept_16_3_2_15_1_7367 35 50 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 50 143 (accept_3_2 34 50 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 50 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 50 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 50 143
  (Polychromatic418967fa.accept_7_4_1_3_1_277 32 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 50 143 (accept_3_2 31 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  50 143 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 50 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 50 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 143 (accept_3_2 28 50 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 50 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 50 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 143
  (Polychromatic418967fa.accept_7_5_1_3_1_103 26 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 50 143 (accept_3_2 25 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  50 143 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 50 143 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 50 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 143 (accept_3_2 22 50 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 50 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 50 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 50 143
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 50 143 (accept_3_2 19 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  50 143 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 50 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 50 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 143 (accept_3_2 16 50 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 50 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 50 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 50 143
  (Polychromatic418967fa.accept_15_14_5_8_1_3175 14 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 50 143 (accept_3_2 13 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  50 143 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 50 143 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 50 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 50 143 (accept_3_2 10 50 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 50 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 50 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 143
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 50 143 (accept_3_2 7 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50
  143 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 50 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 50 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 50 143 (accept_3_2 4 50 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 50 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 50 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 143 (Polychromatic418967fa.accept_7_2_1_3_1_102 2
  50 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 50 143 (accept_3_2 1 50 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 143)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  49 143 (allA_of_3_0 49 49 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 48 143 (allA_succ_of_accept 47 48
  143 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 48 143 (accept_3_2 46 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  48 143 (Polychromatic418967fa.accept_10_5_8_3_1_229 45 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 48 143 (Polychromatic418967fa.accept_7_2_6_3_1_100 44 48 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 143 (accept_3_2 43 48 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 48 143 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 48 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 48 143
  (Polychromatic418967fa.accept_9_5_3_8_1_316 41 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 48 143 (accept_3_2 40 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  48 143 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 48 143 (Polychromatic418967fa.accept_9_2_3_8_1_318 38 48 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 143 (accept_3_2 37 48 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 143 (Polychromatic418967fa.accept_10_6_8_3_1_930 36 48 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 48 143
  (Polychromatic418967fa.accept_10_5_8_3_1_229 35 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 48 143 (accept_3_2 34 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  48 143 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 48 143 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 48 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 143 (accept_3_2 31 48 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 143 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 48 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 48 143
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 48 143 (accept_3_2 28 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  48 143 (Polychromatic418967fa.accept_15_12_3_8_1_5245 27 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 48 143 (Polychromatic418967fa.accept_10_6_8_3_1_930 26 48 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 143 (accept_3_2 25 48 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 143 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 48 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 48 143
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 48 143 (accept_3_2 22 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  48 143 (Polychromatic418967fa.accept_10_1_8_3_1_947 21 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 48 143 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 48 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 143 (accept_3_2 19 48 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 48 143 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 48 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 48 143
  (Polychromatic418967fa.accept_22_17_4_11_1_7403 17 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 48 143 (accept_3_2 16 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  48 143 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 48 143 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 48 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 143 (accept_3_2 13 48 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 48 143 (Polychromatic418967fa.accept_15_12_3_8_1_5245 12 48 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 48 143
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 48 143 (accept_3_2 10 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  48 143 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 48 143 (Polychromatic418967fa.accept_17_8_14_7_1_6203 8 48 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 143 (accept_3_2 7 48 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 143 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 48 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 48 143
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 48 143 (accept_3_2 4 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 48
  143 (Polychromatic418967fa.accept_23_3_2_5_1_7402 3 48 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 48 143 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 48 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 143 (accept_3_2 1 48 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 48 143)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 143
  (allA_succ_of_accept 46 47 143 (accept_3_2 46 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  47 143 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 47 143 (Polychromatic418967fa.accept_7_2_5_3_1_98 44 47 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 143 (accept_3_2 43 47 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 47 143 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 47 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 143
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 47 143 (accept_3_2 40 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  47 143 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 47 143 (Polychromatic418967fa.accept_18_2_11_17_1_4773 38 47 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 143 (accept_3_2 37 47 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 47 143 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 47 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 143
  (Polychromatic418967fa.accept_10_5_7_3_1_561 35 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 143 (accept_3_2 34 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 143 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 143 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 47 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 143 (accept_3_2 31 47 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 143 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 47 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 143
  (Polychromatic418967fa.accept_7_1_5_3_1_268 29 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 143 (accept_3_2 28 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 143 (Polychromatic418967fa.accept_23_4_1_5_1_7401 27 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 143 (Polychromatic418967fa.accept_10_6_7_3_1_547 26 47 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 143 (accept_3_2 25 47 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 143 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 47 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 143
  (Polychromatic418967fa.accept_7_2_5_3_1_98 23 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 143 (accept_3_2 22 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 143 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 143 (Polychromatic418967fa.accept_18_2_11_17_1_4773 20 47 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 143 (accept_3_2 19 47 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 143 (Polychromatic418967fa.accept_19_18_9_10_1_4698 18 47
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 143
  (Polychromatic418967fa.accept_25_17_22_18_1_7400 17 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 47 143 (accept_3_2 16 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 47 143 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 47 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 47 143 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 47 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 143 (accept_3_2 13 47 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 143 (Polychromatic418967fa.accept_9_3_2_8_1_108 12
  47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 143
  (Polychromatic418967fa.accept_17_11_13_7_1_3795 11 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 143 (accept_3_2 10 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 143 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 143 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 47 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 143 (accept_3_2 7 47 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 143 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 47 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 143
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 143 (accept_3_2 4 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  143 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 47 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 143 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 47 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 143 (accept_3_2 1 47 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 143))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 143 (allA_of_3_0 46 46 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 45 143 (allA_succ_of_accept 44 45 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 143 (accept_3_2 43 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  45 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 45 143 (Polychromatic418967fa.accept_19_3_7_10_1_6023 41 45 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 143 (accept_3_2 40 45 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 143 (Polychromatic418967fa.accept_12_3_9_11_1_231 39 45 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 143
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 143 (accept_3_2 37 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  45 143 (Polychromatic418967fa.accept_19_17_7_10_1_1171 36 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 45 143 (Polychromatic418967fa.accept_16_3_13_15_1_1913 35 45 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 143 (accept_3_2 34 45 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 143 (Polychromatic418967fa.accept_18_15_9_17_1_6043 33 45
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 143 (accept_3_2 31 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  45 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 45 143 (Polychromatic418967fa.accept_21_8_3_17_1_7399 29 45 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 143 (accept_3_2 28 45 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 143 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 45 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 143
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 143 (accept_3_2 25 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  45 143 (Polychromatic418967fa.accept_19_5_7_10_1_7375 24 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 45 143 (Polychromatic418967fa.accept_21_2_3_17_1_7398 23 45 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 143 (accept_3_2 22 45 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 143 (Polychromatic418967fa.accept_20_1_5_3_1_7397 21 45 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 45 143 (accept_3_2 19 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  45 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 45 143 (Polychromatic418967fa.accept_10_7_5_3_1_542 17 45 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 143 (accept_3_2 16 45 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 143 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 45 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 143
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 143 (accept_3_2 13 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  45 143 (Polychromatic418967fa.accept_10_2_5_3_1_1408 12 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 45 143 (Polychromatic418967fa.accept_25_11_20_18_1_3852 11 45 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 143 (accept_3_2 10 45 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 143 (Polychromatic418967fa.accept_19_9_7_10_1_1170 9 45 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 143 (accept_3_2 7 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45
  143 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 45 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 143 (Polychromatic418967fa.accept_17_5_11_7_1_6146 5 45 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 143 (accept_3_2 4 45 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 45 143 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 45 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 45
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 143 (accept_3_2 1 45 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 143))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  143 (allA_succ_of_accept 43 44 143 (accept_3_2 43 44 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 44 143 (Polychromatic418967fa.accept_19_4_6_10_1_7396 42 44 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 44 143 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 44 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 143 (accept_3_2 40 44 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 44 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 44 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 143
  (Polychromatic418967fa.accept_12_2_8_11_1_31 38 44 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 44 143 (accept_3_2 37 44 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  44 143 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 44 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 44 143 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 44 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 143 (accept_3_2 34 44 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 33 44 143 11 3 4 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 32 44 143 (Polychromatic418967fa.accept_19_13_6_10_1_7395 32 44 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 44 143 (accept_3_2 31 44 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 44 143 (Polychromatic418967fa.accept_21_9_2_17_1_7394 30 44
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 44 143
  (Polychromatic418967fa.accept_7_1_2_3_1_257 29 44 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 44 143 (accept_3_2 28 44 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  44 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 44 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 44 143 (Polychromatic418967fa.accept_7_5_2_3_1_106 26 44 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 44 143 (accept_3_2 25 44 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 44 143 (Polychromatic418967fa.accept_15_9_14_8_1_1396 24 44 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 44 143
  (Polychromatic418967fa.accept_18_5_8_17_1_3478 23 44 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 44 143 11 2 4 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 44 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 44 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 44 143 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 44 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 44 143 (accept_3_2 19 44 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 44 143
  (Polychromatic418967fa.accept_16_2_12_15_1_2908 18 44 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 44 143 (Polychromatic418967fa.accept_10_7_4_3_1_560 17 44 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 44 143 (accept_3_2 16 44 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 44 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 44 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 44 143 (Polychromatic418967fa.accept_12_2_8_11_1_31
  14 44 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 44 143 (accept_3_2 13
  44 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 44 143
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 44 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 11 44 143 11 1 4 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 10 44 143 (accept_3_2 10 44 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  44 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 44 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 44 143 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 44 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 44 143 (accept_3_2 7 44 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 44 143 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 44 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 44 143
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 44 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 44 143 (accept_3_2 4 44 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 44
  143 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 44 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 44 143 (Polychromatic418967fa.accept_12_2_8_11_1_31 2 44 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 143 (accept_3_2 1 44 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 44 143)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 143 (allA_of_3_0 43 43 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 143 (allA_succ_of_accept 41 42 143
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 42 143 (accept_3_2 40 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  42 143 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 42 143 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 42 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 143 (accept_3_2 37 42 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 143 (Polychromatic418967fa.accept_19_17_4_10_1_7371 36 42 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 42 143
  (Polychromatic418967fa.accept_10_5_2_3_1_239 35 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 42 143 (accept_3_2 34 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  42 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 42 143 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 42 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 143 (accept_3_2 31 42 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 42 143 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 42 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 42 143
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 42 143 (accept_3_2 28 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  42 143 (Polychromatic418967fa.accept_16_11_10_15_1_6301 27 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 42 143 (Polychromatic418967fa.accept_15_11_12_8_1_739 26 42 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 143 (accept_3_2 25 42 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 143 (Polychromatic418967fa.accept_22_2_20_11_1_5852 24 42
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 42 143
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 42 143 (accept_3_2 22 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  42 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 42 143 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 42 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 143 (accept_3_2 19 42 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 42 143 (Polychromatic418967fa.accept_15_3_12_8_1_738 18 42 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 42 143
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 42 143 (accept_3_2 16 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  42 143 (Polychromatic418967fa.accept_10_5_2_3_1_239 15 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 42 143 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 42 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 143 (accept_3_2 13 42 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 143 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 42 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 42 143
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 42 143 (accept_3_2 10 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  42 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 42 143 (Polychromatic418967fa.accept_19_8_4_10_1_7393 8 42 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 143 (accept_3_2 7 42 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 42 143 (Polychromatic418967fa.accept_19_6_4_10_1_3342 6 42 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 42 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 42
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42 143 (accept_3_2 4 42 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 42 143 (Polychromatic418967fa.accept_9_3_6_8_1_308 3
  42 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 42 143
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 42 143 (accept_3_2 1 42 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42
  143)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 143 (allA_succ_of_accept 40 41 143 (accept_3_2 40 41 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 143 (Polychromatic418967fa.accept_7_4_6_3_1_271 39
  41 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 41 143
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 41 143 (accept_3_2 37 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  41 143 (Polychromatic418967fa.accept_22_14_19_11_1_7392 36 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 41 143 (Polychromatic418967fa.accept_15_5_11_8_1_1391 35 41 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 143 (accept_3_2 34 41 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 143 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 41 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 41 143
  (Polychromatic418967fa.accept_7_4_6_3_1_271 32 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 41 143 (accept_3_2 31 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  41 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 41 143 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 41 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 143 (accept_3_2 28 41 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 41 143 (Polychromatic418967fa.accept_15_12_11_8_1_1392 27 41 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 143
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 41 143 (accept_3_2 25 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  41 143 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 41 143 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 41 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 143 (accept_3_2 22 41 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 41 143 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 41 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 41 143
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 41 143 (accept_3_2 19 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  41 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 41 143 (Polychromatic418967fa.accept_23_17_18_5_1_7391 17 41 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 143 (accept_3_2 16 41 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 143 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 41 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 143
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 41 143 (accept_3_2 13 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  41 143 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 41 143 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 41 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 143 (accept_3_2 10 41 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 41 143 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 41 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 143
  (Polychromatic418967fa.accept_10_8_1_3_1_1374 8 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 41 143 (accept_3_2 7 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41
  143 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 41 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 41 143 (Polychromatic418967fa.accept_15_5_11_8_1_1391 5 41 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 143 (accept_3_2 4 41 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 41 143 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 41 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 41
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 143 (accept_3_2 1 41 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41 143))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 143
  (allA_of_3_0 40 40 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 143 (allA_succ_of_accept 38 39 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 39 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 143 (accept_3_2 37 39 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 143 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 39 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 143 (Polychromatic418967fa.accept_14_7_11_3_1_5365 35 39 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 143 (accept_3_2 34 39 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 143 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 39 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 39 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 143 (accept_3_2 31 39 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 143 (Polychromatic418967fa.accept_16_14_7_15_1_3947 30 39 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 143 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 39 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 143 (accept_3_2 28 39 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 143 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 39 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 39 143 13 2 3 11 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 39 143 (accept_3_2 25 39 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 39 143 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 39 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 39 143
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 39 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 39 143 (accept_3_2 22 39 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  39 143 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 39 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 39 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 39 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 143 (accept_3_2 19 39 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 39 143 (Polychromatic418967fa.accept_15_3_9_8_1_3164 18 39 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 39 143
  (Polychromatic418967fa.accept_15_2_9_8_1_736 17 39 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 39 143 (accept_3_2 16 39 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  39 143 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 39 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 39 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 39 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13 39 143 13 1 3 11 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12 39 143 (Polychromatic418967fa.accept_17_12_5_7_1_6179
  12 39 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 39 143
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 39 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 39 143 (accept_3_2 10 39 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  39 143 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 39 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 39 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 39 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 143 (accept_3_2 7 39 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 39 143 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 39 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 39 143
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 39 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 39 143 (accept_3_2 4 39 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 39
  143 (Polychromatic418967fa.accept_15_3_9_8_1_3164 3 39 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 39 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 39 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 143 (accept_3_2 1 39 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 39 143))))))))))))))))))))))))))))))))))))))) (allB_succ 38 143 (allA_succ_of_accept 37
  38 143 (accept_3_2 37 38 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 38 143
  (Polychromatic418967fa.accept_10_6_8_3_1_930 36 38 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 38 143 (Polychromatic418967fa.accept_10_5_8_3_1_229 35 38 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 143 (accept_3_2 34 38 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 38 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 38 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 143 (Polychromatic418967fa.accept_9_5_2_8_1_109 32
  38 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 38 143 (accept_3_2 31 38
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 38 143
  (Polychromatic418967fa.accept_9_3_2_8_1_108 30 38 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 38 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 38 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 143 (accept_3_2 28 38 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 38 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 38 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 143 (Polychromatic418967fa.accept_10_6_8_3_1_930
  26 38 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 38 143 (accept_3_2 25
  38 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 38 143
  (Polychromatic418967fa.accept_9_6_2_8_1_592 24 38 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 38 143 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 38 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 143 (accept_3_2 22 38 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 38 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 38 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 143 (Polychromatic418967fa.accept_12_8_2_11_1_246
  20 38 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 38 143 (accept_3_2 19
  38 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 38 143
  (Polychromatic418967fa.accept_22_18_16_11_1_7390 18 38 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 38 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 38 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 143 (accept_3_2 16 38 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 38 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 143
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 38 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 38 143 (accept_3_2 13 38 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  38 143 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 38 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 38 143 (Polychromatic418967fa.accept_10_1_8_3_1_947 11 38 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 143 (accept_3_2 10 38 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 38 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 143
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 38 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 143 (accept_3_2 7 38 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  143 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 38 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 38 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 38 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 143 (accept_3_2 4 38 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 38 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 38 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 143 (Polychromatic418967fa.accept_20_2_18_3_1_4519
  2 38 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 143 (accept_3_2 1 38
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 143)))))))))))))))))))))))))))))))))))))) (allB_succ 37 143
  (allA_of_3_0 37 37 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 36 143 (allA_succ_of_accept 35 36 143
  (Polychromatic418967fa.accept_8_3_4_7_1_475 35 36 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 36 143 (accept_3_2 34 36 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  36 143 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 36 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 36 143 (Polychromatic418967fa.accept_7_4_1_3_1_277 32 36 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 143 (accept_3_2 31 36 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 36 143 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 36 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 36 143
  (Polychromatic418967fa.accept_10_9_6_3_1_545 29 36 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 36 143 (accept_3_2 28 36 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  36 143 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 36 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 36 143 (Polychromatic418967fa.accept_7_5_1_3_1_103 26 36 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 143 (accept_3_2 25 36 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 36 143 (Polychromatic418967fa.accept_16_8_4_15_1_2941 24 36 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 36 143
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 36 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 36 143 (accept_3_2 22 36 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  36 143 (Polychromatic418967fa.accept_16_5_4_15_1_1102 21 36 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 36 143 (Polychromatic418967fa.accept_19_1_17_10_1_4689 20 36 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 143 (accept_3_2 19 36 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 143 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 36 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 36 143
  (Polychromatic418967fa.accept_10_7_6_3_1_927 17 36 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 36 143 (accept_3_2 16 36 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  36 143 (Polychromatic418967fa.accept_17_15_2_7_1_7389 15 36 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 36 143 (Polychromatic418967fa.accept_15_14_6_8_1_1410 14 36 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 143 (accept_3_2 13 36 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 36 143 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 36 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 36 143
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 36 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 36 143 (accept_3_2 10 36 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  36 143 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 36 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 36 143 (Polychromatic418967fa.accept_10_8_6_3_1_1394 8 36 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 143 (accept_3_2 7 36 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 36 143 (Polychromatic418967fa.accept_21_6_15_17_1_7388 6 36 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 36 143
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 36 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 36 143 (accept_3_2 4 36 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 36
  143 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 36 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 36 143 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 36 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 143 (accept_3_2 1 36 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 36 143)))))))))))))))))))))))))))))))))))) (allB_succ 35 143 (allA_succ_of_accept 34 35 143
  (accept_3_2 34 35 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 143
  (Polychromatic418967fa.accept_15_3_5_8_1_1387 33 35 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 143 (Polychromatic418967fa.accept_10_2_5_3_1_1408 32 35 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 143 (accept_3_2 31 35 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 35 143 (Polychromatic418967fa.accept_20_10_15_3_1_7387 30 35 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 143
  (Polychromatic418967fa.accept_15_14_5_8_1_3175 29 35 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 35 143 (accept_3_2 28 35 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  35 143 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 35 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 35 143 (Polychromatic418967fa.accept_15_11_5_8_1_3157 26 35 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 143 (accept_3_2 25 35 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 35 143 (Polychromatic418967fa.accept_14_10_7_3_1_1022 24 35
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 143
  (Polychromatic418967fa.accept_16_7_3_15_1_2940 23 35 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 35 143 (accept_3_2 22 35 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  35 143 (Polychromatic418967fa.accept_28_21_7_3_1_7386 21 35 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 35 143 (Polychromatic418967fa.accept_8_4_3_7_1_491 20 35 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 35 143 (accept_3_2 19 35 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 35 143 (Polychromatic418967fa.accept_10_8_5_3_1_543 18 35 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 143
  (Polychromatic418967fa.accept_10_7_5_3_1_542 17 35 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 35 143 (accept_3_2 16 35 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  35 143 (Polychromatic418967fa.accept_21_15_14_17_1_5940 15 35 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 35 143 (Polychromatic418967fa.accept_15_14_5_8_1_3175 14 35 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 143 (accept_3_2 13 35 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 143 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 35 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 143
  (Polychromatic418967fa.accept_14_11_7_3_1_3416 11 35 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 35 143 (accept_3_2 10 35 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  35 143 (Polychromatic418967fa.accept_19_9_16_10_1_4701 9 35 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 35 143 (Polychromatic418967fa.accept_10_8_5_3_1_543 8 35 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 143 (accept_3_2 7 35 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 35 143 (Polychromatic418967fa.accept_19_6_16_10_1_7385 6 35 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 143
  (Polychromatic418967fa.accept_19_5_16_10_1_7384 5 35 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 35 143 (accept_3_2 4 35 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35
  143 (Polychromatic418967fa.accept_15_3_5_8_1_1387 3 35 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 35 143 (Polychromatic418967fa.accept_10_2_5_3_1_1408 2 35 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 143 (accept_3_2 1 35 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 35 143))))))))))))))))))))))))))))))))))) (allB_succ 34 143 (allA_of_3_0 34 34 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 33 143 (allA_succ_of_accept 32 33 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 33 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 143 (accept_3_2 31 33 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  33 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 33 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 33 143 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 33 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 143 (accept_3_2 28 33 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 143 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 33 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 143
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 33 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 143 (accept_3_2 25 33 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  33 143 (Polychromatic418967fa.accept_15_9_3_8_1_3155 24 33 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 33 143 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 33 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 33 143 11 2 3 13 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 33 143 (Polychromatic418967fa.accept_9_3_6_8_1_308 21
  33 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 33 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 33 143 (accept_3_2 19 33 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  33 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 33 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 33 143 (Polychromatic418967fa.accept_23_17_10_5_1_7383 17 33 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 143 (accept_3_2 16 33 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 143 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 33 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 143
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 33 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 143 (accept_3_2 13 33 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  33 143 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 33 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 11 33 143 11 1 3 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 10 33 143 (accept_3_2 10 33 143 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 33 143 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 33 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 33 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 143 (accept_3_2 7 33 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 33
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 143
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 33 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 33 143 (accept_3_2 4 33 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33
  143 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 33 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 33 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 33 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 143 (accept_3_2 1 33 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 33 143))))))))))))))))))))))))))))))))) (allB_succ 32 143 (allA_succ_of_accept 31 32 143
  (accept_3_2 31 32 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 32 143
  (Polychromatic418967fa.accept_9_3_5_8_1_99 30 32 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 32 143 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 32 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 143 (accept_3_2 28 32 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 32 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 32 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 143 (Polychromatic418967fa.accept_12_2_8_11_1_31
  26 32 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 32 143 (accept_3_2 25
  32 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 32 143
  (Polychromatic418967fa.accept_9_6_5_8_1_598 24 32 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 32 143 (Polychromatic418967fa.accept_19_4_13_10_1_7382 23 32 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 143 (accept_3_2 22 32 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 32 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 32 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 143 (Polychromatic418967fa.accept_7_6_4_3_1_266 20
  32 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 32 143 (accept_3_2 19 32
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 32 143
  (Polychromatic418967fa.accept_22_18_10_11_1_7381 18 32 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 32 143 (Polychromatic418967fa.accept_25_17_7_18_1_7380 17 32 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 32 143 (accept_3_2 16 32 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 32 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 32 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 32 143
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 32 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 32 143 (accept_3_2 13 32 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  32 143 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 32 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 32 143 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 32 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 143 (accept_3_2 10 32 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 32 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 32 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 143
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 32 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 32 143 (accept_3_2 7 32 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32
  143 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 32 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 32 143 (Polychromatic418967fa.accept_10_5_2_3_1_239 5 32 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 32 143 (accept_3_2 4 32 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 32 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 32 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 32 143 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 32
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 143 (accept_3_2 1 32 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32 143)))))))))))))))))))))))))))))))) (allB_succ 31 143
  (allA_of_3_0 31 31 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 30 143 (allA_succ_of_accept 29 30 143
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 30 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 30 143 (accept_3_2 28 30 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  30 143 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 30 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 30 143 (Polychromatic418967fa.accept_7_5_2_3_1_106 26 30 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 30 143 (accept_3_2 25 30 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 30 143 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 30 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 30 143
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 30 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 30 143 (accept_3_2 22 30 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  30 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 30 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 30 143 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 30 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 143 (accept_3_2 19 30 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 143 (Polychromatic418967fa.accept_19_18_11_10_1_7379 18 30 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 30 143
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 30 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 30 143 (accept_3_2 16 30 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  30 143 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 30 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 30 143 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 30 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 143 (accept_3_2 13 30 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 143 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 30 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 30 143
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 30 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 30 143 (accept_3_2 10 30 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  30 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 30 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 30 143 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 30 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 143 (accept_3_2 7 30 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 30 143 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 30 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 30 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 30
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 30 143 (accept_3_2 4 30 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 30 143 (Polychromatic418967fa.accept_19_3_11_10_1_2184
  3 30 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 30 143
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 30 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 30 143 (accept_3_2 1 30 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30
  143)))))))))))))))))))))))))))))) (allB_succ 29 143 (allA_succ_of_accept 28 29 143 (accept_3_2 28 29 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 143 (Polychromatic418967fa.accept_22_5_7_11_1_7378 27 29
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 29 143
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 29 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 29 143 (accept_3_2 25 29 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  29 143 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 29 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 29 143 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 29 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 143 (accept_3_2 22 29 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 143 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 29 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 29 143
  (Polychromatic418967fa.accept_15_5_14_8_1_1376 20 29 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 29 143 (accept_3_2 19 29 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  29 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 29 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 29 143 (Polychromatic418967fa.accept_22_17_7_11_1_7377 17 29 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 143 (accept_3_2 16 29 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 143 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 29 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 29 143
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 29 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 29 143 (accept_3_2 13 29 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  29 143 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 29 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 29 143 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 29 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 143 (accept_3_2 10 29 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 29 143 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 29 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 143
  (Polychromatic418967fa.accept_24_8_5_23_1_7376 8 29 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 29 143 (accept_3_2 7 29 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29
  143 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 29 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 29 143 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 29 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 143 (accept_3_2 4 29 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 29 143 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 29 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 29
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 143 (accept_3_2 1 29 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29 143))))))))))))))))))))))))))))) (allB_succ 28 143 (allA_of_3_0
  28 28 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 27 143 (allA_succ_of_accept 26 27 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 27 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 143 (accept_3_2 25 27 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  27 143 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 27 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 27 143 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 27 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 143 (accept_3_2 22 27 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 143 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 27 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 27 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 143 (accept_3_2 19 27 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  27 143 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 27 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 27 143 (Polychromatic418967fa.accept_16_1_11_15_1_498 17 27 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 143 (accept_3_2 16 27 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 143 (Polychromatic418967fa.accept_10_5_7_3_1_561 15 27 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 27 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 143 (accept_3_2 13 27 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  27 143 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 27 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 27 143 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 27 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 143 (accept_3_2 10 27 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 143 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 27 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 27 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 143 (accept_3_2 7 27 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27
  143 (Polychromatic418967fa.accept_10_6_7_3_1_547 6 27 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 27 143 (Polychromatic418967fa.accept_10_5_7_3_1_561 5 27 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 143 (accept_3_2 4 27 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 27 143 (Polychromatic418967fa.accept_15_3_12_8_1_738 3 27 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 27
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 143 (accept_3_2 1 27 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 143))))))))))))))))))))))))))) (allB_succ 26 143
  (allA_succ_of_accept 25 26 143 (accept_3_2 25 26 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  26 143 (Polychromatic418967fa.accept_19_5_7_10_1_7375 24 26 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 26 143 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 26 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 26 143 (accept_3_2 22 26 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 26 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 26 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 26 143
  (Polychromatic418967fa.accept_12_8_2_11_1_246 20 26 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 26 143 (accept_3_2 19 26 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  26 143 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 26 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 26 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 26 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 26 143 (accept_3_2 16 26 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 26 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 26 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 26 143
  (Polychromatic418967fa.accept_16_14_10_15_1_3969 14 26 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 13 26 143 13 1 2 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 12 26 143 (Polychromatic418967fa.accept_15_12_11_8_1_1392 12 26 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 26 143
  (Polychromatic418967fa.accept_16_11_10_15_1_6301 11 26 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 26 143 (accept_3_2 10 26 143 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 26 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 26 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 26 143 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 26 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 26 143 (accept_3_2 7 26 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 26 143 (Polychromatic418967fa.accept_22_6_4_11_1_7374
  6 26 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 26 143
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 26 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 26 143 (accept_3_2 4 26 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 26
  143 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 26 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 26 143 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 26 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 26 143 (accept_3_2 1 26 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 26 143)))))))))))))))))))))))))) (allB_succ 25 143 (allA_of_3_0 25 25 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 24 143 (allA_succ_of_accept 23 24 143 (Polychromatic418967fa.accept_9_5_6_8_1_101 23
  24 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 143 (accept_3_2 22 24
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 24 143
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 24 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 24 143 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 24 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 24 143 (accept_3_2 19 24 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 24 143 (Polychromatic418967fa.accept_15_3_9_8_1_3164 18 24 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 24 143 (Polychromatic418967fa.accept_10_7_4_3_1_560
  17 24 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 143 (accept_3_2 16
  24 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 24 143
  (Polychromatic418967fa.accept_18_15_6_17_1_2386 15 24 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 24 143 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 24 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 143 (accept_3_2 13 24 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 24 143 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 24 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 24 143 (Polychromatic418967fa.accept_9_2_6_8_1_321 11
  24 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 24 143 (accept_3_2 10 24
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 24 143
  (Polychromatic418967fa.accept_10_9_4_3_1_539 9 24 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 24 143 (Polychromatic418967fa.accept_19_8_5_10_1_7373 8 24 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 143 (accept_3_2 7 24 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 24 143 (Polychromatic418967fa.accept_14_6_10_3_1_1038 6 24 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 24 143 (Polychromatic418967fa.accept_9_5_6_8_1_101 5
  24 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24 143 (accept_3_2 4 24 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 24 143 (Polychromatic418967fa.accept_9_3_6_8_1_308 3
  24 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 24 143
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 24 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 24 143 (accept_3_2 1 24 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24
  143)))))))))))))))))))))))) (allB_succ 23 143 (allA_succ_of_accept 22 23 143 (accept_3_2 22 23 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 143 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 23 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 23 143
  (Polychromatic418967fa.accept_7_6_2_3_1_107 20 23 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 23 143 (accept_3_2 19 23 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  23 143 (Polychromatic418967fa.accept_22_18_1_11_1_7372 18 23 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 23 143 (Polychromatic418967fa.accept_19_17_4_10_1_7371 17 23 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 143 (accept_3_2 16 23 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 143 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 23 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 143
  (Polychromatic418967fa.accept_16_14_7_15_1_3947 14 23 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 143 (accept_3_2 13 23 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  23 143 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 23 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 23 143 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 23 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 143 (accept_3_2 10 23 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 143 (Polychromatic418967fa.accept_19_9_4_10_1_7370 9 23 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 143
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 23 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 23 143 (accept_3_2 7 23 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23
  143 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 23 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 23 143 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 23 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 143 (accept_3_2 4 23 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 23 143 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 23 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 143 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 23
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 143 (accept_3_2 1 23 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23 143))))))))))))))))))))))) (allB_succ 22 143 (allA_of_3_0 22 22
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 21 143 (allA_succ_of_accept 20 21 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 21 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 143 (accept_3_2 19 21 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  21 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 21 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 21 143 (Polychromatic418967fa.accept_15_2_6_8_1_754 17 21 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 143 (accept_3_2 16 21 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 143 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 21 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 143
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 21 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 21 143 (accept_3_2 13 21 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  21 143 (Polychromatic418967fa.accept_10_2_1_3_1_233 12 21 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 21 143 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 21 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 143 (accept_3_2 10 21 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 143 (Polychromatic418967fa.accept_27_9_21_8_1_7369 9 21 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 21 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 143 (accept_3_2 7 21 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21
  143 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 21 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 143 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 21 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 143 (accept_3_2 4 21 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 21 143 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 21 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 21
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 143 (accept_3_2 1 21 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 143))))))))))))))))))))) (allB_succ 20 143 (allA_succ_of_accept
  19 20 143 (accept_3_2 19 20 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 20 143
  (Polychromatic418967fa.accept_7_4_6_3_1_271 18 20 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 20 143 (Polychromatic418967fa.accept_19_17_1_10_1_4671 17 20 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 143 (accept_3_2 16 20 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 20 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 20 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 20 143 (Polychromatic418967fa.accept_9_5_2_8_1_109 14
  20 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 20 143 (accept_3_2 13 20
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 20 143
  (Polychromatic418967fa.accept_9_3_2_8_1_108 12 20 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 20 143 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 20 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 20 143 (accept_3_2 10 20 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 20 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 20 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 143 (Polychromatic418967fa.accept_16_8_4_15_1_2941
  8 20 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 20 143 (accept_3_2 7 20
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20 143 (Polychromatic418967fa.accept_9_6_2_8_1_592
  6 20 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 20 143
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 20 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 20 143 (accept_3_2 4 20 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 20
  143 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 20 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 20 143 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 20 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 20 143 (accept_3_2 1 20 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 143)))))))))))))))))))) (allB_succ 19 143 (allA_of_3_0 19 19 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 18 143 (allA_succ_of_accept 17 18 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 18 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 143 (accept_3_2 16 18 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 18 143 (Polychromatic418967fa.accept_7_1_4_3_1_21 15
  18 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 143
  (Polychromatic418967fa.accept_19_14_18_10_1_7368 14 18 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 18 143 (accept_3_2 13 18 143 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 18 143 (Polychromatic418967fa.accept_15_12_3_8_1_5245 12 18 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 18 143 (Polychromatic418967fa.accept_10_1_8_3_1_947 11 18 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 143 (accept_3_2 10 18 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 18 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 18
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 143
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 18 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 18 143 (accept_3_2 7 18 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18
  143 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 18 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 18 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 18 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 143 (accept_3_2 4 18 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 18 143 (Polychromatic418967fa.accept_16_3_2_15_1_7367 3 18 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 18 143 (Polychromatic418967fa.accept_19_2_18_10_1_7366
  2 18 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 143 (accept_3_2 1 18
  143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 143)))))))))))))))))) (allB_succ 17 143 (allA_succ_of_accept
  16 17 143 (accept_3_2 16 17 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 143
  (Polychromatic418967fa.accept_10_5_7_3_1_561 15 17 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 17 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 17 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 143 (accept_3_2 13 17 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 17 143 (Polychromatic418967fa.accept_19_12_17_10_1_7365 12 17 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 143
  (Polychromatic418967fa.accept_16_11_1_15_1_1123 11 17 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 17 143 (accept_3_2 10 17 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  17 143 (Polychromatic418967fa.accept_15_9_2_8_1_1379 9 17 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 17 143 (Polychromatic418967fa.accept_16_8_1_15_1_1982 8 17 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 143 (accept_3_2 7 17 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 17 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 17 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 143
  (Polychromatic418967fa.accept_10_5_7_3_1_561 5 17 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 17 143 (accept_3_2 4 17 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17
  143 (Polychromatic418967fa.accept_26_3_17_13_1_7364 3 17 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 17 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 17 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 143 (accept_3_2 1 17 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 17 143))))))))))))))))) (allB_succ 16 143 (allA_of_3_0 16 16 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 15 143 (allA_succ_of_accept 14 15 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 15
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 143 (accept_3_2 13 15 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 15 143 (Polychromatic418967fa.accept_7_5_1_3_1_103 12
  15 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 143
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 15 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 15 143 (accept_3_2 10 15 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  15 143 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 15 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 15 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 15 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 143 (accept_3_2 7 15 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 143 (Polychromatic418967fa.accept_18_6_15_17_1_7363 6 15 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 15 143
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 15 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 15 143 (accept_3_2 4 15 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 15
  143 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 15 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 15 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 15 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 143 (accept_3_2 1 15 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 15 143))))))))))))))) (allB_succ 14 143 (allA_succ_of_accept 13 14 143 (accept_3_2 13 14 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 14 143 (Polychromatic418967fa.accept_9_3_5_8_1_99 12
  14 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 14 143
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 14 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 14 143 (accept_3_2 10 14 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  14 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 14 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 14 143 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 14 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 14 143 (accept_3_2 7 14 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 14 143 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 14 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 14 143 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 14
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 14 143 (accept_3_2 4 14 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 14 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 14
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 14 143
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 14 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 14 143 (accept_3_2 1 14 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14
  143)))))))))))))) (allB_succ 13 143 (allA_of_3_0 13 13 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 12 143
  (allA_succ_of_accept 11 12 143 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 12 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 143 (accept_3_2 10 12 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 12 143 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 12 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 143 (Polychromatic418967fa.accept_7_1_5_3_1_268 8
  12 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 12 143 (accept_3_2 7 12 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12 143 (Polychromatic418967fa.accept_9_6_3_8_1_595 6
  12 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 12 143
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 12 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 12 143 (accept_3_2 4 12 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 12
  143 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 12 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 12 143 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 12 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12 143 (accept_3_2 1 12 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 12 143)))))))))))) (allB_succ 11 143 (allA_succ_of_accept 10 11 143 (accept_3_2 10 11 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 143 (Polychromatic418967fa.accept_27_9_11_8_1_7362
  9 11 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 11 143
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 11 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 11 143 (accept_3_2 7 11 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 11
  143 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 11 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 11 143 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 11 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 143 (accept_3_2 4 11 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 11 143 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 11 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 143 (Polychromatic418967fa.accept_10_2_1_3_1_233 2
  11 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 11 143 (accept_3_2 1 11 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11 143))))))))))) (allB_succ 10 143 (allA_of_3_0 10 10 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 9 143 (allA_succ_of_accept 8 9 143
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 9 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 9 143 (accept_3_2 7 9 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 143
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 9 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 9 143 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 9 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 143 (accept_3_2 4 9 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 9 143 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 9 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 143 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 9
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 143 (accept_3_2 1 9 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 143))))))))) (allB_succ 8 143 (allA_succ_of_accept 7 8 143
  (accept_3_2 7 8 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 8 143
  (Polychromatic418967fa.accept_10_6_8_3_1_930 6 8 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 8 143 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 8 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 8 143 (accept_3_2 4 8 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 8 143 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 8 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 8 143 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 8
  143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 8 143 (accept_3_2 1 8 143
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 143)))))))) (allB_succ 7 143 (allA_of_3_0 7 7 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 6 143 (allA_succ_of_accept 5 6 143
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 6 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 143 (accept_3_2 4 6 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 6 143
  (Polychromatic418967fa.accept_9_3_6_8_1_308 3 6 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 6 143 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 6 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 143 (accept_3_2 1 6 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 6 143)))))) (allB_succ 5 143 (allA_succ_of_accept 4 5 143 (accept_3_2 4 5 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 143 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 5 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 143
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 5 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 5 143 (accept_3_2 1 5 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 143)))))
  (allB_succ 4 143 (allA_of_3_0 4 4 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 3 143 (allA_succ_of_accept 2
  3 143 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 3 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 3 143 (accept_3_2 1 3 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 143)))
  (allB_succ 2 143 (allA_succ_of_accept 1 2 143 (accept_3_2 1 2 143 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2
  143)) (allB_two
  143)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


