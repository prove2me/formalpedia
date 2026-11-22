-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch142
-- name    : Polychromatic418967fa_Branch142
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:14:18.273754+00:00
-- url     : https://prove2.me/theorems/4e5913e3-a535-47b6-8fa7-ddfc36092581
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

def Polychromatic418967fa.branch_142 : allB 142 142 :=
  allB_succ' 2 141 142 (Eq.refl Bool.true) (allA_succ_of_accept 1 141 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  141 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 141 142)) (allB_succ' 3 140 142
  (Eq.refl Bool.true) (allA_of_3_1 3 140 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 139 142 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 139 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 139 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 139 142 (accept_3_3 2 139 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 139 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 139 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 139 142)))) (allB_succ' 5 138 142 (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 138 142 2 2 69 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 138 142 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 138 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 138 142 2 1 69 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 138 142 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 138 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138 142))))) (allB_succ' 6 137 142 (Eq.refl
  Bool.true) (allA_of_3_1 6 137 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 136 142 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 136 142 2 3 68 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 136 142 (accept_3_3 5 136 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 136
  142 2 2 68 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  136 142 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 136 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 136 142 2 1 68 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 136 142 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 136 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 136 142))))))) (allB_succ' 8 135 142 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 135 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 135 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 135 142 (Polychromatic418967fa.accept_12_6_3_10_1_224 6 135 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 135 142 (accept_3_3 5 135 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 135 142 (Polychromatic418967fa.accept_13_4_5_12_1_751
  4 135 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 135 142
  (Polychromatic418967fa.accept_10_3_5_2_1_38 3 135 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 135 142 (accept_3_3 2 135 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  135 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 135 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 135 142)))))))) (allB_succ' 9 134 142 (Eq.refl Bool.true) (allA_of_3_1 9 134 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 133 142 (Eq.refl Bool.true) (allA_succ_of_accept 9 133 142
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 133 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 133 142 (accept_3_3 8 133 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  133 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 133 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 133 142 (Polychromatic418967fa.accept_15_6_13_7_1_222 6 133 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 133 142 (accept_3_3 5 133 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 133 142 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 133 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 133 142
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 133 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 133 142 (accept_3_3 2 133 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  133 142 (Polychromatic418967fa.accept_10_1_3_2_1_220 1 133 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 133 142)))))))))) (allB_succ' 11 132 142 (Eq.refl Bool.true) (allA_succ_of_gcd 10 132 142 2 5 66
  71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 132 142
  (Polychromatic418967fa.accept_16_9_4_14_1_1878 9 132 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 132 142 2 4 66 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 132 142 (Polychromatic418967fa.accept_16_7_4_14_1_2860 7 132 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132 142 2 3 66 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 132 142 (accept_3_3 5 132 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 132 142 2 2 66 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 132 142 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 132 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 132 142 2 1 66 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 132 142 (Polychromatic418967fa.accept_7_1_6_2_1_18 1
  132 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132 142))))))))))) (allB_succ' 12 131
  142 (Eq.refl Bool.true) (allA_of_3_1 12 131 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 130 142
  (Eq.refl Bool.true) (allA_succ_of_gcd 12 130 142 2 6 65 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 130 142 (accept_3_3 11 130 142 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 130 142 2 5 65 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 130 142 (Polychromatic418967fa.accept_14_9_4_2_1_983 9 130 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 130 142 2 4 65 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 130 142 (Polychromatic418967fa.accept_18_7_4_16_1_2299 7 130 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 130 142 2 3 65 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 130 142 (accept_3_3 5 130 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 130 142 2 2 65 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 130 142 (Polychromatic418967fa.accept_9_3_4_7_1_89 3
  130 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 130 142 2 1 65 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 130 142
  (Polychromatic418967fa.accept_9_1_4_7_1_7 1 130 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 130 142))))))))))))) (allB_succ' 14 129 142 (Eq.refl Bool.true) (allA_succ_of_accept 13 129 142
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 129 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 129 142 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 129 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 129 142 (accept_3_3 11 129 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 129 142 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 129 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 129 142 (Polychromatic418967fa.accept_11_9_8_10_1_934
  9 129 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 129 142 (accept_3_3 8
  129 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 142
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 129 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 129 142 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 129 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 129 142 (accept_3_3 5 129 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 129 142 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 129 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 129 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 3
  129 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 129 142 (accept_3_3 2 129
  142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 142 (Polychromatic418967fa.accept_6_1_3_4_1_1
  1 129 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129 142)))))))))))))) (allB_succ' 15
  128 142 (Eq.refl Bool.true) (allA_of_3_1 15 128 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 127 142
  (Eq.refl Bool.true) (allA_succ_of_accept 15 127 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 127 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 127 142 (accept_3_3 14 127 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 127 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 127 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 127 142
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 127 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 127 142 (accept_3_3 11 127 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 127 142 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 127 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 127 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 127 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 127 142 (accept_3_3 8 127 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 127 142 (Polychromatic418967fa.accept_13_7_10_12_1_2047 7 127 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 127 142
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 127 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 127 142 (accept_3_3 5 127 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  127 142 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 127 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 127 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 127 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 127 142 (accept_3_3 2 127 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 127 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 127 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 127 142)))))))))))))))) (allB_succ' 17 126 142 (Eq.refl
  Bool.true) (allA_succ_of_gcd 16 126 142 2 8 63 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 126 142 (Polychromatic418967fa.accept_11_4_5_10_1_926 15 126 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 126 142 2 7 63 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 126 142
  (Polychromatic418967fa.accept_15_13_6_7_1_1369 13 126 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 126 142 2 6 63 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 126 142 (accept_3_3 11 126 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  126 142 2 5 63 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 126 142 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 126 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 126 142 2 4 63 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 126 142 (Polychromatic418967fa.accept_22_7_16_10_1_7361 7 126 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 126 142 2 3 63 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 126 142 (accept_3_3 5 126 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 126 142 2 2 63 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 126 142 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 126 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 126 142 2 1 63 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 126 142
  (Polychromatic418967fa.accept_10_1_6_2_1_867 1 126 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 126 142))))))))))))))))) (allB_succ' 18 125 142 (Eq.refl Bool.true) (allA_of_3_1 18 125 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 124 142 (Eq.refl Bool.true) (allA_succ_of_gcd 18 124 142 2 9 62 71
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 124 142
  (accept_3_3 17 124 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 124 142 2 8 62 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 124 142
  (Polychromatic418967fa.accept_19_15_10_9_1_5956 15 124 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 124 142 2 7 62 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 124 142 (Polychromatic418967fa.accept_12_1_4_10_1_209 13 124 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 124 142 2 6 62 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 124 142 (accept_3_3 11 124 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 124 142 2 5 62 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 124 142
  (Polychromatic418967fa.accept_20_9_4_2_1_1900 9 124 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 124 142 2 4 62 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 124 142 (Polychromatic418967fa.accept_10_7_4_2_1_903 7 124 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 124 142 2 3 62 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 124 142 (accept_3_3 5 124 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 124 142 2 2 62 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 124 142 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 124 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 124 142 2 1 62 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 124 142 (Polychromatic418967fa.accept_12_1_4_10_1_209 1
  124 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 124 142))))))))))))))))))) (allB_succ'
  20 123 142 (Eq.refl Bool.true) (allA_succ_of_accept 19 123 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 123 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 123 142
  (Polychromatic418967fa.accept_12_6_3_10_1_224 18 123 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 123 142 (accept_3_3 17 123 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 123 142 (Polychromatic418967fa.accept_27_16_15_7_1_7360 16 123 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 123 142 (Polychromatic418967fa.accept_10_5_3_2_1_899 15 123 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 123 142 (accept_3_3 14 123 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 123 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 123 142
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 123 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 123 142 (accept_3_3 11 123 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 123 142 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 123 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 123 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 123 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 123 142 (accept_3_3 8 123 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 123 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 142
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 123 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 123 142 (accept_3_3 5 123 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  123 142 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 123 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 123 142 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 123 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 123 142 (accept_3_3 2 123 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 123 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 123 142)))))))))))))))))))) (allB_succ' 21 122 142
  (Eq.refl Bool.true) (allA_of_3_1 21 122 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 121 142 (Eq.refl
  Bool.true) (allA_succ_of_accept 21 121 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 121 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 121 142 (accept_3_3 20 121 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 121 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 121 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 121 142
  (Polychromatic418967fa.accept_13_5_4_12_1_2058 18 121 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 121 142 (accept_3_3 17 121 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 121 142 (Polychromatic418967fa.accept_10_6_1_2_1_874 16 121 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 121 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 121 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 121 142 (accept_3_3 14 121 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 121 142 (Polychromatic418967fa.accept_10_3_1_2_1_521 13 121 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 121 142
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 121 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 121 142 (accept_3_3 11 121 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 121 142 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 121 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 121 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 121 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 121 142 (accept_3_3 8 121 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 121 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 121 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 121 142
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 121 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 121 142 (accept_3_3 5 121 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  121 142 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 121 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 121 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 121 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 121 142 (accept_3_3 2 121 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 121 142 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 121 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 121 142)))))))))))))))))))))) (allB_succ' 23 120 142
  (Eq.refl Bool.true) (allA_succ_of_gcd 22 120 142 2 11 60 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 120 142 (Polychromatic418967fa.accept_25_21_20_17_1_7359 21 120
  142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 120 142 2 10 60 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 120 142
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 120 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 120 142 2 9 60 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 120 142 (accept_3_3 17 120 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  120 142 2 8 60 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 120 142 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 120 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 120 142 2 7 60 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 120 142 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 120 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 142 2 6 60 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 142 (accept_3_3 11 120 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 120 142 2 5 60 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 120 142
  (Polychromatic418967fa.accept_13_9_3_12_1_2025 9 120 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 120 142 2 4 60 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 120 142 (Polychromatic418967fa.accept_29_7_4_26_1_7358 7 120 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120 142 2 3 60 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 120 142 (accept_3_3 5 120 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 120 142 2 2 60 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 120 142 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 120 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 120 142 2 1 60 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 120 142 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 120
  142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120 142))))))))))))))))))))))) (allB_succ'
  24 119 142 (Eq.refl Bool.true) (allA_of_3_1 24 119 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 118 142
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 118 142 2 12 59 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 118 142 (accept_3_3 23 118 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 118 142 2 11 59 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 118 142 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 118 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 118 142 2 10 59 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 118 142
  (Polychromatic418967fa.accept_18_1_10_16_1_566 19 118 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 118 142 2 9 59 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 118 142 (accept_3_3 17 118 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  118 142 2 8 59 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 118 142 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 118 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 118 142 2 7 59 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 118 142 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 118 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 118 142 2 6 59 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 118 142 (accept_3_3 11 118 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 118 142 2 5 59 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 118 142
  (Polychromatic418967fa.accept_11_9_8_10_1_934 9 118 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 118 142 2 4 59 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 118 142 (Polychromatic418967fa.accept_17_7_16_6_1_3705 7 118 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 118 142 2 3 59 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 118 142 (accept_3_3 5 118 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 118 142 2 2 59 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 118 142 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 118 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 118 142 2 1 59 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 118 142 (Polychromatic418967fa.accept_7_1_6_2_1_18 1
  118 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118 142)))))))))))))))))))))))))
  (allB_succ' 26 117 142 (Eq.refl Bool.true) (allA_succ_of_accept 25 117 142 (Polychromatic418967fa.accept_6_1_3_4_1_1
  25 117 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 117 142
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 117 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 117 142 (accept_3_3 23 117 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 117 142 (Polychromatic418967fa.accept_26_22_13_12_1_7357 22 117 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 117 142 (Polychromatic418967fa.accept_14_7_5_2_1_2473 21 117 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 117 142 (accept_3_3 20 117 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 117 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 117 142
  (Polychromatic418967fa.accept_7_4_5_2_1_243 18 117 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 117 142 (accept_3_3 17 117 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 117 142 (Polychromatic418967fa.accept_22_16_7_10_1_7356 16 117 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 117 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 117 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 142 (accept_3_3 14 117 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 117 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 117 142
  (Polychromatic418967fa.accept_18_12_9_16_1_4732 12 117 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 117 142 (accept_3_3 11 117 142 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 117 142 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 117 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 142 (Polychromatic418967fa.accept_10_9_7_2_1_887 9 117 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 142 (accept_3_3 8 117 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 7
  117 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 142
  (Polychromatic418967fa.accept_12_6_9_10_1_565 6 117 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 117 142 (accept_3_3 5 117 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  117 142 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 117 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 117 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 117 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 142 (accept_3_3 2 117 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 117 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117 142)))))))))))))))))))))))))) (allB_succ' 27 116 142
  (Eq.refl Bool.true) (allA_of_3_1 27 116 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 115 142 (Eq.refl
  Bool.true) (allA_succ_of_accept 27 115 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 115 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 115 142 (accept_3_3 26 115 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 115 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 115 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 115 142
  (Polychromatic418967fa.accept_17_7_13_6_1_811 24 115 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 115 142 (accept_3_3 23 115 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 115 142 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 115 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 115 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 115 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 115 142 (accept_3_3 20 115 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 115 142 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 115 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 115 142
  (Polychromatic418967fa.accept_10_8_5_2_1_881 18 115 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 115 142 (accept_3_3 17 115 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 115 142 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 115 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 115 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 115 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 115 142 (accept_3_3 14 115 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 115 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 115 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 115 142
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 115 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 115 142 (accept_3_3 11 115 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 115 142 (Polychromatic418967fa.accept_13_10_11_12_1_1320 10 115 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 115 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 115 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 115 142 (accept_3_3 8 115 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 115 142 (Polychromatic418967fa.accept_10_7_5_2_1_880 7 115 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 115 142
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 115 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 115 142 (accept_3_3 5 115 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  115 142 (Polychromatic418967fa.accept_11_4_5_10_1_926 4 115 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 115 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 115 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 142 (accept_3_3 2 115 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 115 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 115 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115 142)))))))))))))))))))))))))))) (allB_succ' 29 114
  142 (Eq.refl Bool.true) (allA_succ_of_gcd 28 114 142 2 14 57 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 114 142 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 114 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 114 142 2 13 57 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 114 142
  (Polychromatic418967fa.accept_21_4_9_16_1_7355 25 114 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 114 142 2 12 57 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 114 142 (accept_3_3 23 114 142 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 114 142 2 11 57 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 114 142 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 114 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 114 142 2 10 57 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 114 142
  (Polychromatic418967fa.accept_9_1_6_7_1_285 19 114 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 142 2 9 57 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 114 142 (accept_3_3 17 114 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  114 142 2 8 57 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 114 142 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 114 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 114 142 2 7 57 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 114 142 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 114 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 114 142 2 6 57 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 114 142 (accept_3_3 11 114 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 114 142 2 5 57 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 114 142
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 114 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 114 142 2 4 57 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 114 142 (Polychromatic418967fa.accept_10_7_4_2_1_903 7 114 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114 142 2 3 57 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 114 142 (accept_3_3 5 114 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 114 142 2 2 57 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 114 142 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 114 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 114 142 2 1 57 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 142 (Polychromatic418967fa.accept_9_1_6_7_1_285 1
  114 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114 142)))))))))))))))))))))))))))))
  (allB_succ' 30 113 142 (Eq.refl Bool.true) (allA_of_3_1 30 113 142 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 31 112 142 (Eq.refl Bool.true) (allA_succ_of_gcd 30 112 142 2 15 56 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 112 142 (accept_3_3 29 112 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 112 142 2 14 56 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 112 142 (Polychromatic418967fa.accept_13_1_8_12_1_2045
  27 112 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 112 142 2 13 56 71
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 112 142
  (Polychromatic418967fa.accept_12_1_4_10_1_209 25 112 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 112 142 2 12 56 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 112 142 (accept_3_3 23 112 142 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 112 142 2 11 56 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 112 142 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 112 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 112 142 2 10 56 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 112 142
  (Polychromatic418967fa.accept_9_1_4_7_1_7 19 112 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 112 142 2 9 56 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 112 142 (accept_3_3 17 112 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  112 142 2 8 56 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 112 142 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 112 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 112 142 2 7 56 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 112 142 (Polychromatic418967fa.accept_12_1_4_10_1_209 13 112 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 112 142 2 6 56 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 112 142 (accept_3_3 11 112 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 112 142 2 5 56 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 112 142
  (Polychromatic418967fa.accept_13_9_8_12_1_2031 9 112 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 112 142 2 4 56 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 112 142 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 112 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 112 142 2 3 56 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 112 142 (accept_3_3 5 112 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 112 142 2 2 56 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 112 142 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 112 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 112 142 2 1 56 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 112 142 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 112
  142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112 142)))))))))))))))))))))))))))))))
  (allB_succ' 32 111 142 (Eq.refl Bool.true) (allA_succ_of_accept 31 111 142 (Polychromatic418967fa.accept_6_1_3_4_1_1
  31 111 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 111 142
  (Polychromatic418967fa.accept_12_6_3_10_1_224 30 111 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 111 142 (accept_3_3 29 111 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 111 142 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 111 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 111 142 (Polychromatic418967fa.accept_15_12_6_7_1_1353 27 111 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 111 142 (accept_3_3 26 111 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 111 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 142
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 111 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 111 142 (accept_3_3 23 111 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 111 142 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 111 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 111 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 111 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 111 142 (accept_3_3 20 111 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 111 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 142
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 111 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 111 142 (accept_3_3 17 111 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 111 142 (Polychromatic418967fa.accept_10_6_1_2_1_874 16 111 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 111 142 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 111 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 111 142 (accept_3_3 14 111 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 111 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 142
  (Polychromatic418967fa.accept_15_12_6_7_1_1353 12 111 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 111 142 (accept_3_3 11 111 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 111 142 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 111 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 111 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 111 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 142 (accept_3_3 8 111 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 111 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 142
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 111 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 111 142 (accept_3_3 5 111 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  111 142 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 111 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 111 142 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 111 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 142 (accept_3_3 2 111 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 111 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111 142)))))))))))))))))))))))))))))))) (allB_succ' 33
  110 142 (Eq.refl Bool.true) (allA_of_3_1 33 110 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 109 142
  (Eq.refl Bool.true) (allA_succ_of_accept 33 109 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 109 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 109 142 (accept_3_3 32 109 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 109 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 109 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 109 142
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 109 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 109 142 (accept_3_3 29 109 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 109 142 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 109 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 109 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 109 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 109 142 (accept_3_3 26 109 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 109 142 (Polychromatic418967fa.accept_15_10_4_7_1_3127 25 109 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 109 142
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 109 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 109 142 (accept_3_3 23 109 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 109 142 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 109 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 109 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 109 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 109 142 (accept_3_3 20 109 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 109 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 109 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 109 142
  (Polychromatic418967fa.accept_15_3_4_7_1_1352 18 109 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 109 142 (accept_3_3 17 109 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 109 142 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 109 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 109 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 109 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 109 142 (accept_3_3 14 109 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 109 142 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 109 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 109 142
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 109 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 109 142 (accept_3_3 11 109 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 109 142 (Polychromatic418967fa.accept_15_10_4_7_1_3127 10 109 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 109 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 109 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 109 142 (accept_3_3 8 109 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 109 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 109 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 109 142
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 109 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 109 142 (accept_3_3 5 109 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  109 142 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 109 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 109 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 109 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 109 142 (accept_3_3 2 109 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 109 142 (Polychromatic418967fa.accept_10_1_9_2_1_45 1 109 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 109 142)))))))))))))))))))))))))))))))))) (allB_succ' 35
  108 142 (Eq.refl Bool.true) (allA_succ_of_gcd 34 108 142 2 17 54 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 108 142 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 108 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 108 142 2 16 54 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 108 142
  (Polychromatic418967fa.accept_13_5_4_12_1_2058 31 108 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 108 142 2 15 54 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 108 142 (accept_3_3 29 108 142 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 108 142 2 14 54 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 108 142 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 108 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 108 142 2 13 54 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 108 142
  (Polychromatic418967fa.accept_10_5_8_2_1_517 25 108 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 108 142 2 12 54 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 108 142 (accept_3_3 23 108 142 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 108 142 2 11 54 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 108 142 (Polychromatic418967fa.accept_13_8_4_12_1_2753 21 108 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 108 142 2 10 54 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 108 142
  (Polychromatic418967fa.accept_7_5_3_2_1_249 19 108 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 108 142 2 9 54 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 108 142 (accept_3_3 17 108 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  108 142 2 8 54 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 108 142 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 108 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 108 142 2 7 54 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 108 142 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 108 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 108 142 2 6 54 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 108 142 (accept_3_3 11 108 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 108 142 2 5 54 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 108 142
  (Polychromatic418967fa.accept_21_9_3_16_1_1684 9 108 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 108 142 2 4 54 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 108 142 (Polychromatic418967fa.accept_13_7_4_12_1_1341 7 108 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 142 2 3 54 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 142 (accept_3_3 5 108 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 108 142 2 2 54 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 108 142 (Polychromatic418967fa.accept_13_3_4_12_1_36 3 108 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 108 142 2 1 54 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 108 142 (Polychromatic418967fa.accept_7_1_3_2_1_13 1
  108 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  142))))))))))))))))))))))))))))))))))) (allB_succ' 36 107 142 (Eq.refl Bool.true) (allA_of_3_1 36 107 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 106 142 (Eq.refl Bool.true) (allA_succ_of_gcd 36 106 142 2 18 53 71
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 106 142
  (accept_3_3 35 106 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 106 142 2 17 53 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 106 142
  (Polychromatic418967fa.accept_19_14_11_9_1_3330 33 106 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 106 142 2 16 53 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 106 142 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 106 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 106 142 2 15 53 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 106 142 (accept_3_3 29 106 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 106 142 2 14 53 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 106 142
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 106 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 106 142 2 13 53 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 106 142 (Polychromatic418967fa.accept_11_3_7_10_1_180 25 106 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 106 142 2 12 53 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 106 142 (accept_3_3 23 106 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 106 142 2 11 53 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 106 142
  (Polychromatic418967fa.accept_10_1_6_2_1_867 21 106 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 106 142 2 10 53 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 106 142 (Polychromatic418967fa.accept_13_6_2_12_1_2802 19 106 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 106 142 2 9 53 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 106 142 (accept_3_3 17 106 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 106 142 2 8 53 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 106 142
  (Polychromatic418967fa.accept_14_1_8_2_1_1675 15 106 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 106 142 2 7 53 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 106 142 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 106 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 106 142 2 6 53 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 106 142 (accept_3_3 11 106 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 106 142 2 5 53 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 106 142 (Polychromatic418967fa.accept_15_9_1_7_1_1350 9 106 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 106 142 2 4 53 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 106 142
  (Polychromatic418967fa.accept_16_7_10_14_1_1884 7 106 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 106 142 2 3 53 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 106 142 (accept_3_3 5 106 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 106
  142 2 2 53 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  106 142 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 106 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 106 142 2 1 53 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 106 142 (Polychromatic418967fa.accept_10_1_6_2_1_867 1 106 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106 142))))))))))))))))))))))))))))))))))))) (allB_succ' 38 105 142
  (Eq.refl Bool.true) (allA_succ_of_accept 37 105 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 105 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 105 142
  (Polychromatic418967fa.accept_16_4_9_14_1_3883 36 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 105 142 (accept_3_3 35 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 105 142 (Polychromatic418967fa.accept_13_8_1_12_1_762 34 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 105 142 (Polychromatic418967fa.accept_10_3_5_2_1_38 33 105 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 142 (accept_3_3 32 105 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 105 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 105 142
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 105 142 (accept_3_3 29 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 105 142 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 105 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 105 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 142 (accept_3_3 26 105 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 105 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 105 142
  (Polychromatic418967fa.accept_13_11_1_12_1_742 24 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 105 142 (accept_3_3 23 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 105 142 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 105 142 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 105 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 105 142 (accept_3_3 20 105 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 105 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 142
  (Polychromatic418967fa.accept_10_8_5_2_1_881 18 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 105 142 (accept_3_3 17 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 105 142 (Polychromatic418967fa.accept_11_5_6_10_1_1432 16 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 105 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 105 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 105 142 (accept_3_3 14 105 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 105 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 142
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 105 142 (accept_3_3 11 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 105 142 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 105 142 (Polychromatic418967fa.accept_14_9_7_2_1_2483 9 105 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 105 142 (accept_3_3 8 105 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 105 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 105 142
  (Polychromatic418967fa.accept_12_6_9_10_1_565 6 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 105 142 (accept_3_3 5 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  105 142 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 105 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 105 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 142 (accept_3_3 2 105 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 105 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105 142))))))))))))))))))))))))))))))))))))))
  (allB_succ' 39 104 142 (Eq.refl Bool.true) (allA_of_3_1 39 104 142 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 40 103 142 (Eq.refl Bool.true) (allA_succ_of_accept 39 103 142 (Polychromatic418967fa.accept_6_3_1_4_1_25
  39 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 103 142 (accept_3_3 38
  103 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 103 142
  (Polychromatic418967fa.accept_4_1_3_2_1_3 37 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 103 142 (Polychromatic418967fa.accept_15_6_13_7_1_222 36 103 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 103 142 (accept_3_3 35 103 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 103 142 (Polychromatic418967fa.accept_21_13_19_16_1_721 34 103 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 103 142
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 103 142 (accept_3_3 32 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 103 142 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 103 142 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 103 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 103 142 (accept_3_3 29 103 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 103 142 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 103 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 103 142
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 103 142 (accept_3_3 26 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 103 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 103 142 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 103 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 103 142 (accept_3_3 23 103 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 103 142 (Polychromatic418967fa.accept_17_5_1_6_1_2615 22 103 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 103 142
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 103 142 (accept_3_3 20 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 103 142 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 103 142 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 103 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 103 142 (accept_3_3 17 103 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 103 142 (Polychromatic418967fa.accept_11_5_4_10_1_524 16 103 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 103 142
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 103 142 (accept_3_3 14 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 103 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 103 142 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 103 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 103 142 (accept_3_3 11 103 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 103 142 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 103 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 103 142
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 103 142 (accept_3_3 8 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  103 142 (Polychromatic418967fa.accept_14_7_5_2_1_2473 7 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 103 142 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 103 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 103 142 (accept_3_3 5 103 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 103 142 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 103 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 103 142
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 103 142 (accept_3_3 2 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  103 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 103 142)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 102 142 (Eq.refl Bool.true)
  (allA_succ_of_gcd 40 102 142 2 20 51 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 102 142 (Polychromatic418967fa.accept_12_3_6_10_1_576 39 102 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 102 142 2 19 51 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 102 142
  (Polychromatic418967fa.accept_9_1_3_7_1_6 37 102 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 142 2 18 51 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 102 142 (accept_3_3 35 102 142 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 102 142 2 17 51 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 102 142 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 102 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 102 142 2 16 51 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 102 142
  (Polychromatic418967fa.accept_9_4_3_7_1_296 31 102 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 142 2 15 51 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 102 142 (accept_3_3 29 102 142 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 102 142 2 14 51 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 102 142 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 102 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 102 142 2 13 51 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 102 142
  (Polychromatic418967fa.accept_15_10_12_7_1_1358 25 102 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 102 142 2 12 51 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 102 142 (accept_3_3 23 102 142 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 102 142 2 11 51 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 102 142 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 102 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 102 142 2 10 51 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 102 142
  (Polychromatic418967fa.accept_7_5_4_2_1_235 19 102 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 142 2 9 51 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 102 142 (accept_3_3 17 102 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  102 142 2 8 51 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 102 142 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 102 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 102 142 2 7 51 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 102 142 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 102 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 102 142 2 6 51 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 102 142 (accept_3_3 11 102 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 102 142 2 5 51 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 102 142
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 102 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 102 142 2 4 51 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 102 142 (Polychromatic418967fa.accept_11_7_3_10_1_1461 7 102 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102 142 2 3 51 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 102 142 (accept_3_3 5 102 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 102 142 2 2 51 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 102 142 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 102 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 102 142 2 1 51 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 142 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 102
  142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  142))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 101 142 (Eq.refl Bool.true) (allA_of_3_1 42 101 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 100 142 (Eq.refl Bool.true) (allA_succ_of_gcd 42 100 142 2 21
  50 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 100 142
  (accept_3_3 41 100 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 100 142 2 20 50 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 100 142
  (Polychromatic418967fa.accept_9_3_1_7_1_97 39 100 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 100 142 2 19 50 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 100 142 (Polychromatic418967fa.accept_12_1_4_10_1_209 37 100 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 100 142 2 18 50 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 100 142 (accept_3_3 35 100 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 100 142 2 17 50 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 100 142
  (Polychromatic418967fa.accept_9_6_1_7_1_577 33 100 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 100 142 2 16 50 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 100 142 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 100 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 100 142 2 15 50 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 100 142 (accept_3_3 29 100 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 100 142 2 14 50 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 100 142
  (Polychromatic418967fa.accept_15_12_10_7_1_1357 27 100 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 100 142 2 13 50 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 100 142 (Polychromatic418967fa.accept_12_1_4_10_1_209 25 100 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 100 142 2 12 50 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 100 142 (accept_3_3 23 100 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 100 142 2 11 50 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 100 142
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 100 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 100 142 2 10 50 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 100 142 (Polychromatic418967fa.accept_12_7_4_10_1_572 19 100 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 100 142 2 9 50 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 100 142 (accept_3_3 17 100 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 100 142 2 8 50 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 100 142
  (Polychromatic418967fa.accept_9_6_1_7_1_577 15 100 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 100 142 2 7 50 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 100 142 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 100 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 100 142 2 6 50 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 100 142 (accept_3_3 11 100 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 100 142 2 5 50 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 100 142 (Polychromatic418967fa.accept_11_9_1_10_1_920 9 100 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 100 142 2 4 50 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 100 142
  (Polychromatic418967fa.accept_12_7_4_10_1_572 7 100 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 100 142 2 3 50 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 100 142 (accept_3_3 5 100 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 100
  142 2 2 50 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  100 142 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 100 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 100 142 2 1 50 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 100 142 (Polychromatic418967fa.accept_12_1_4_10_1_209 1 100 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 100 142))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44
  99 142 (Eq.refl Bool.true) (allA_succ_of_accept 43 99 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 99 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 99 142
  (Polychromatic418967fa.accept_12_6_3_10_1_224 42 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 99 142 (accept_3_3 41 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  99 142 (Polychromatic418967fa.accept_13_1_8_12_1_2045 40 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 99 142 (Polychromatic418967fa.accept_21_18_15_16_1_2917 39 99 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 99 142 (accept_3_3 38 99 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 99 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 99 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 99 142
  (Polychromatic418967fa.accept_13_10_8_12_1_2032 36 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 99 142 (accept_3_3 35 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  99 142 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 99 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 99 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 99 142 (accept_3_3 32 99 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 99 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 99 142
  (Polychromatic418967fa.accept_12_6_3_10_1_224 30 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 99 142 (accept_3_3 29 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  99 142 (Polychromatic418967fa.accept_15_13_9_7_1_2194 28 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 99 142 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 99 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 99 142 (accept_3_3 26 99 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 99 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 99 142
  (Polychromatic418967fa.accept_7_3_1_2_1_247 24 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 99 142 (accept_3_3 23 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  99 142 (Polychromatic418967fa.accept_13_9_8_12_1_2031 22 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 99 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 99 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 99 142 (accept_3_3 20 99 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 99 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 99 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 99 142
  (Polychromatic418967fa.accept_12_6_3_10_1_224 18 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 99 142 (accept_3_3 17 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  99 142 (Polychromatic418967fa.accept_15_1_9_7_1_3130 16 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 99 142 (Polychromatic418967fa.accept_17_15_14_6_1_7354 15 99 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 99 142 (accept_3_3 14 99 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 99 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 99 142
  (Polychromatic418967fa.accept_18_12_9_16_1_4732 12 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 99 142 (accept_3_3 11 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  99 142 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 99 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 99 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 142 (accept_3_3 8 99 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 99 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99 142
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 99 142 (accept_3_3 5 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99
  142 (Polychromatic418967fa.accept_13_4_8_12_1_3526 4 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 99 142 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 99 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 142 (accept_3_3 2 99 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 99 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99 142))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 45 98 142 (Eq.refl Bool.true) (allA_of_3_1 45 98 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  46 97 142 (Eq.refl Bool.true) (allA_succ_of_accept 45 97 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 97 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 97 142 (accept_3_3 44 97 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 97 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 43
  97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 97 142
  (Polychromatic418967fa.accept_19_4_2_9_1_4584 42 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 97 142 (accept_3_3 41 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  97 142 (Polychromatic418967fa.accept_12_4_1_10_1_221 40 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 97 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 97 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 97 142 (accept_3_3 38 97 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 97 142 (Polychromatic418967fa.accept_18_1_7_16_1_1342 37 97 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 97 142
  (Polychromatic418967fa.accept_7_1_6_2_1_18 36 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 97 142 (accept_3_3 35 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  97 142 (Polychromatic418967fa.accept_10_4_7_2_1_211 34 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 97 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 97 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 97 142 (accept_3_3 32 97 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 97 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 97 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 97 142
  (Polychromatic418967fa.accept_11_8_9_10_1_503 30 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 97 142 (accept_3_3 29 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  97 142 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 97 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 97 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 97 142 (accept_3_3 26 97 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 97 142 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 97 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 97 142
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 97 142 (accept_3_3 23 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  97 142 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 97 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 97 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 97 142 (accept_3_3 20 97 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 97 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 97 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 97 142
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 97 142 (accept_3_3 17 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  97 142 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 97 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 97 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 97 142 (accept_3_3 14 97 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 97 142 (Polychromatic418967fa.accept_16_13_1_14_1_2855 13 97 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 97 142
  (Polychromatic418967fa.accept_11_1_9_10_1_184 12 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 97 142 (accept_3_3 11 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  97 142 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 97 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 97 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 142 (accept_3_3 8 97 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 97 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 97 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 142
  (Polychromatic418967fa.accept_21_6_13_16_1_7353 6 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 97 142 (accept_3_3 5 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97
  142 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 97 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 97 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 142 (accept_3_3 2 97 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 97 142 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 97 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97 142)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47
  96 142 (Eq.refl Bool.true) (allA_succ_of_gcd 46 96 142 2 23 48 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 96 142 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 96 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 96 142 2 22 48 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 96 142
  (Polychromatic418967fa.accept_13_4_5_12_1_751 43 96 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 96 142 2 21 48 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 96 142 (accept_3_3 41 96 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 96
  142 2 20 48 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  96 142 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 96 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 96 142 2 19 48 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 96 142 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 96 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 96 142 2 18 48 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 96 142 (accept_3_3 35 96 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 96 142 2 17 48 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 96 142
  (Polychromatic418967fa.accept_13_7_5_12_1_1305 33 96 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 96 142 2 16 48 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 96 142 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 96 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 96 142 2 15 48 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 96 142 (accept_3_3 29 96 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 96 142 2 14 48 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 96 142 (Polychromatic418967fa.accept_13_1_5_12_1_306 27 96 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 96 142 2 13 48 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 96 142
  (Polychromatic418967fa.accept_7_4_5_2_1_243 25 96 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 96 142 2 12 48 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 96 142 (accept_3_3 23 96 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 96
  142 2 11 48 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  96 142 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 96 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 96 142 2 10 48 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 96 142 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 96 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 142 2 9 48 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 142 (accept_3_3 17 96 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 96 142 2 8 48 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 96 142 (Polychromatic418967fa.accept_13_2_5_12_1_2043 15 96 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 96 142 2 7 48 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 96 142
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 96 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 96 142 2 6 48 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 96 142 (accept_3_3 11 96 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 96
  142 2 5 48 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  96 142 (Polychromatic418967fa.accept_11_9_8_10_1_934 9 96 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 96 142 2 4 48 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 96 142 (Polychromatic418967fa.accept_13_7_5_12_1_1305 7 96 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 142 2 3 48 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96 142 (accept_3_3 5 96 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 96 142 2 2 48 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 96 142 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 96 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 96 142 2 1 48 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 96 142
  (Polychromatic418967fa.accept_9_1_6_7_1_285 1 96 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 96 142))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 95 142 (Eq.refl Bool.true) (allA_of_3_1
  48 95 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 94 142 (Eq.refl Bool.true) (allA_succ_of_gcd 48 94
  142 2 24 47 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  94 142 (accept_3_3 47 94 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 94 142 2 23 47 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 94 142
  (Polychromatic418967fa.accept_21_3_10_16_1_4340 45 94 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 94 142 2 22 47 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 94 142 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 94 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 94 142 2 21 47 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 94 142 (accept_3_3 41 94 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 94 142 2 20 47 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 94 142 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 94 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 94 142 2 19 47 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 94 142
  (Polychromatic418967fa.accept_9_1_4_7_1_7 37 94 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 94 142 2 18 47 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 94 142 (accept_3_3 35 94 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 94
  142 2 17 47 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  94 142 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 94 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 94 142 2 16 47 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 94 142 (Polychromatic418967fa.accept_19_12_18_9_1_7352 31 94 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 94 142 2 15 47 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 94 142 (accept_3_3 29 94 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 94 142 2 14 47 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 94 142
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 94 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 94 142 2 13 47 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 94 142 (Polychromatic418967fa.accept_15_10_4_7_1_3127 25 94 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 94 142 2 12 47 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 94 142 (accept_3_3 23 94 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 94 142 2 11 47 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 94 142 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 94 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 94 142 2 10 47 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 94 142
  (Polychromatic418967fa.accept_7_5_3_2_1_249 19 94 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 94 142 2 9 47 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 94 142 (accept_3_3 17 94 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 94
  142 2 8 47 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  94 142 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 94 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 94 142 2 7 47 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 94 142 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 94 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 94 142 2 6 47 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 94 142 (accept_3_3 11 94 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 94 142 2 5 47 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 94 142 (Polychromatic418967fa.accept_13_9_3_12_1_2025 9 94 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 94 142 2 4 47 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 94 142
  (Polychromatic418967fa.accept_10_7_4_2_1_903 7 94 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 94 142 2 3 47 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 94 142 (accept_3_3 5 94 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 94 142
  2 2 47 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 94
  142 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 94 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 94 142 2 1 47 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 94 142 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 94 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 94 142))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 93
  142 (Eq.refl Bool.true) (allA_succ_of_accept 49 93 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 93 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 93 142
  (Polychromatic418967fa.accept_11_4_5_10_1_926 48 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 93 142 (accept_3_3 47 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  93 142 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 93 142 (Polychromatic418967fa.accept_10_5_3_2_1_899 45 93 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 93 142 (accept_3_3 44 93 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 93 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 93 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 93 142
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 93 142 (accept_3_3 41 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  93 142 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 93 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 93 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 93 142 (accept_3_3 38 93 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 93 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 93 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 93 142
  (Polychromatic418967fa.accept_13_10_2_12_1_1332 36 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 93 142 (accept_3_3 35 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  93 142 (Polychromatic418967fa.accept_15_4_3_7_1_713 34 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 93 142 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 93 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 93 142 (accept_3_3 32 93 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 93 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 93 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 93 142
  (Polychromatic418967fa.accept_12_6_9_10_1_565 30 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 93 142 (accept_3_3 29 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  93 142 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 93 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 93 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 142 (accept_3_3 26 93 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 93 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 93 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 93 142
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 93 142 (accept_3_3 23 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  93 142 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 93 142 (Polychromatic418967fa.accept_10_1_3_2_1_220 21 93 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 142 (accept_3_3 20 93 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 93 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 93 142
  (Polychromatic418967fa.accept_12_6_9_10_1_565 18 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 93 142 (accept_3_3 17 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  93 142 (Polychromatic418967fa.accept_13_3_2_12_1_2797 16 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 93 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 93 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 142 (accept_3_3 14 93 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 93 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 93 142
  (Polychromatic418967fa.accept_15_12_3_7_1_4123 12 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 93 142 (accept_3_3 11 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  93 142 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 93 142 (Polychromatic418967fa.accept_17_9_8_6_1_6050 9 93 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 142 (accept_3_3 8 93 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 93 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93 142
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 142 (accept_3_3 5 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93
  142 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 93 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 93 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 142 (accept_3_3 2 93 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 93 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 93 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93 142))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 51 92 142 (Eq.refl Bool.true) (allA_of_3_1 51 92 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  52 91 142 (Eq.refl Bool.true) (allA_succ_of_accept 51 91 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 91 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 91 142 (accept_3_3 50 91 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 91 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 49
  91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 91 142
  (Polychromatic418967fa.accept_9_3_1_7_1_97 48 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 91 142 (accept_3_3 47 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  91 142 (Polychromatic418967fa.accept_10_6_1_2_1_874 46 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 91 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 91 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 91 142 (accept_3_3 44 91 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 91 142 (Polychromatic418967fa.accept_10_3_1_2_1_521 43 91 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 91 142
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 91 142 (accept_3_3 41 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  91 142 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 91 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 91 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 91 142 (accept_3_3 38 91 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 91 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 91 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 91 142
  (Polychromatic418967fa.accept_10_6_1_2_1_874 36 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 91 142 (accept_3_3 35 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  91 142 (Polychromatic418967fa.accept_21_13_7_16_1_7351 34 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 91 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 91 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 91 142 (accept_3_3 32 91 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 91 142 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 91 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 91 142
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 91 142 (accept_3_3 29 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  91 142 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 91 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 91 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 91 142 (accept_3_3 26 91 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 91 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 91 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 91 142
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 91 142 (accept_3_3 23 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  91 142 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 91 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 91 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 91 142 (accept_3_3 20 91 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 91 142 (Polychromatic418967fa.accept_10_9_1_2_1_522 19 91 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 91 142
  (Polychromatic418967fa.accept_11_7_3_10_1_1461 18 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 91 142 (accept_3_3 17 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  91 142 (Polychromatic418967fa.accept_10_6_1_2_1_874 16 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 91 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 91 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 91 142 (accept_3_3 14 91 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 91 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 91 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 91 142
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 91 142 (accept_3_3 11 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  91 142 (Polychromatic418967fa.accept_15_10_1_7_1_5207 10 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 91 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 91 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 142 (accept_3_3 8 91 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 91 142 (Polychromatic418967fa.accept_11_7_3_10_1_1461 7 91 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 91 142
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 91 142 (accept_3_3 5 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91
  142 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 91 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 91 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 142 (accept_3_3 2 91 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 91 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 91 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91 142))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 53 90 142 (Eq.refl Bool.true) (allA_succ_of_gcd 52 90 142 2 26 45 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 90 142
  (Polychromatic418967fa.accept_12_3_6_10_1_576 51 90 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 90 142 2 25 45 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 90 142 (Polychromatic418967fa.accept_19_11_14_9_1_4599 49 90 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 90 142 2 24 45 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 90 142 (accept_3_3 47 90 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 90 142 2 23 45 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 90 142 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 90 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 90 142 2 22 45 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 90 142
  (Polychromatic418967fa.accept_7_1_6_2_1_18 43 90 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 90 142 2 21 45 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 90 142 (accept_3_3 41 90 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 90
  142 2 20 45 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  90 142 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 90 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 90 142 2 19 45 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 90 142 (Polychromatic418967fa.accept_16_5_10_14_1_5074 37 90 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 90 142 2 18 45 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 90 142 (accept_3_3 35 90 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 90 142 2 17 45 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 90 142
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 90 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 90 142 2 16 45 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 90 142 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 90 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90 142 2 15 45 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 90 142 (accept_3_3 29 90 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 90 142 2 14 45 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 90 142 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 90 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 90 142 2 13 45 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 90 142
  (Polychromatic418967fa.accept_7_4_6_2_1_451 25 90 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 90 142 2 12 45 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 90 142 (accept_3_3 23 90 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 90
  142 2 11 45 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  90 142 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 90 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 90 142 2 10 45 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 90 142 (Polychromatic418967fa.accept_27_19_9_7_1_7350 19 90 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 90 142 2 9 45 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 90 142 (accept_3_3 17 90 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90 142 2 8 45 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 90 142 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 90 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 90 142 2 7 45 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 90 142
  (Polychromatic418967fa.accept_16_13_10_14_1_2871 13 90 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 90 142 2 6 45 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 90 142 (accept_3_3 11 90 142 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 90 142 2 5 45 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 90 142 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 90 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 90 142 2 4 45 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 90 142 (Polychromatic418967fa.accept_16_7_10_14_1_1884 7 90 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 142 2 3 45 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 90 142 (accept_3_3 5 90 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 90 142 2 2 45 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 90 142 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 90
  142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 90 142 2 1 45 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 90 142
  (Polychromatic418967fa.accept_7_1_6_2_1_18 1 90 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 90 142))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 89 142 (Eq.refl Bool.true)
  (allA_of_3_1 54 89 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 55 88 142 (Eq.refl Bool.true)
  (allA_succ_of_gcd 54 88 142 2 27 44 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 88 142 (accept_3_3 53 88 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 88
  142 2 26 44 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  88 142 (Polychromatic418967fa.accept_14_9_4_2_1_983 51 88 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 88 142 2 25 44 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 88 142 (Polychromatic418967fa.accept_12_1_4_10_1_209 49 88 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 88 142 2 24 44 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 88 142 (accept_3_3 47 88 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 88 142 2 23 44 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 88 142
  (Polychromatic418967fa.accept_10_5_8_2_1_517 45 88 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 88 142 2 22 44 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 88 142 (Polychromatic418967fa.accept_12_7_4_10_1_572 43 88 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 88 142 2 21 44 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 88 142 (accept_3_3 41 88 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 88 142 2 20 44 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 88 142 (Polychromatic418967fa.accept_15_9_13_7_1_1361 39 88 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 88 142 2 19 44 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 88 142
  (Polychromatic418967fa.accept_12_1_4_10_1_209 37 88 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 88 142 2 18 44 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 88 142 (accept_3_3 35 88 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 88
  142 2 17 44 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  88 142 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 88 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 88 142 2 16 44 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 88 142 (Polychromatic418967fa.accept_12_7_4_10_1_572 31 88 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 88 142 2 15 44 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 88 142 (accept_3_3 29 88 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 88 142 2 14 44 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 88 142
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 88 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 88 142 2 13 44 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 88 142 (Polychromatic418967fa.accept_10_5_8_2_1_517 25 88 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 88 142 2 12 44 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 88 142 (accept_3_3 23 88 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 88 142 2 11 44 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 88 142 (Polychromatic418967fa.accept_13_8_10_12_1_1337 21 88
  142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 88 142 2 10 44 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 88 142
  (Polychromatic418967fa.accept_7_5_4_2_1_235 19 88 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 88 142 2 9 44 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 88 142 (accept_3_3 17 88 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 88
  142 2 8 44 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  88 142 (Polychromatic418967fa.accept_10_5_8_2_1_517 15 88 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 88 142 2 7 44 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 88 142 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 88 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 88 142 2 6 44 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 88 142 (accept_3_3 11 88 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 88 142 2 5 44 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 88 142 (Polychromatic418967fa.accept_13_9_10_12_1_2048 9 88 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 88 142 2 4 44 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 88 142
  (Polychromatic418967fa.accept_12_7_4_10_1_572 7 88 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 88 142 2 3 44 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 88 142 (accept_3_3 5 88 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 88 142
  2 2 44 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 88
  142 (Polychromatic418967fa.accept_19_3_12_9_1_3308 3 88 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 88 142 2 1 44 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 88 142 (Polychromatic418967fa.accept_12_1_4_10_1_209 1 88 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88 142)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 56 87 142 (Eq.refl Bool.true) (allA_succ_of_accept 55 87 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 55
  87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 87 142
  (Polychromatic418967fa.accept_7_5_3_2_1_249 54 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 87 142 (accept_3_3 53 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  87 142 (Polychromatic418967fa.accept_16_4_7_14_1_3897 52 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 87 142 (Polychromatic418967fa.accept_15_6_12_7_1_1360 51 87 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 87 142 (accept_3_3 50 87 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 87 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 87 142
  (Polychromatic418967fa.accept_7_6_3_2_1_461 48 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 87 142 (accept_3_3 47 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  87 142 (Polychromatic418967fa.accept_9_1_6_7_1_285 46 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 87 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 87 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 87 142 (accept_3_3 44 87 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 87 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 87 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 87 142
  (Polychromatic418967fa.accept_12_6_3_10_1_224 42 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 87 142 (accept_3_3 41 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  87 142 (Polychromatic418967fa.accept_7_5_3_2_1_249 40 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 87 142 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 87 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 87 142 (accept_3_3 38 87 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 87 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 87 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 87 142
  (Polychromatic418967fa.accept_7_1_3_2_1_13 36 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 87 142 (accept_3_3 35 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  87 142 (Polychromatic418967fa.accept_7_6_3_2_1_461 34 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 87 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 87 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 87 142 (accept_3_3 32 87 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 87 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 87 142
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 87 142 (accept_3_3 29 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  87 142 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 87 142 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 87 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 87 142 (accept_3_3 26 87 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 87 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 87 142
  (Polychromatic418967fa.accept_10_4_7_2_1_211 24 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 87 142 (accept_3_3 23 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  87 142 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 87 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 87 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 87 142 (accept_3_3 20 87 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 87 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 87 142
  (Polychromatic418967fa.accept_12_6_3_10_1_224 18 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 87 142 (accept_3_3 17 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  87 142 (Polychromatic418967fa.accept_13_3_9_12_1_2062 16 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 87 142 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 87 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 142 (accept_3_3 14 87 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 87 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 87 142
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 87 142 (accept_3_3 11 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  87 142 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 87 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 87 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 142 (accept_3_3 8 87 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 87 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87 142
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 87 142 (accept_3_3 5 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87
  142 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 87 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 87 142 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 87 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 142 (accept_3_3 2 87 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 87 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 87 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87 142))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 57 86 142 (Eq.refl Bool.true) (allA_of_3_1 57 86 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  58 85 142 (Eq.refl Bool.true) (allA_succ_of_accept 57 85 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 85 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 85 142 (accept_3_3 56 85 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 85 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 55
  85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 85 142
  (Polychromatic418967fa.accept_24_6_13_22_1_7332 54 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 85 142 (accept_3_3 53 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  85 142 (Polychromatic418967fa.accept_7_3_1_2_1_247 52 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 85 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 85 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 85 142 (accept_3_3 50 85 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 85 142 (Polychromatic418967fa.accept_13_10_7_12_1_2782 49 85 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 85 142
  (Polychromatic418967fa.accept_7_6_1_2_1_230 48 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 85 142 (accept_3_3 47 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  85 142 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 85 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 85 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 85 142 (accept_3_3 44 85 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 85 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 85 142
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 85 142 (accept_3_3 41 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  85 142 (Polychromatic418967fa.accept_12_4_1_10_1_221 40 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 85 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 85 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 85 142 (accept_3_3 38 85 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 85 142 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 85 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 142
  (Polychromatic418967fa.accept_13_10_7_12_1_2782 36 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 85 142 (accept_3_3 35 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  85 142 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 85 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 85 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 142 (accept_3_3 32 85 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 85 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 85 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 85 142
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 85 142 (accept_3_3 29 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  85 142 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 85 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 85 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 142 (accept_3_3 26 85 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 85 142 (Polychromatic418967fa.accept_16_9_5_14_1_6126 25 85 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 85 142
  (Polychromatic418967fa.accept_7_3_1_2_1_247 24 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 85 142 (accept_3_3 23 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  85 142 (Polychromatic418967fa.accept_14_8_1_2_1_965 22 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 85 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 85 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 85 142 (accept_3_3 20 85 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 85 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 85 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 142
  (Polychromatic418967fa.accept_10_8_5_2_1_881 18 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 85 142 (accept_3_3 17 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  85 142 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 85 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 85 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 85 142 (accept_3_3 14 85 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 142 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 85 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 142
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 142 (accept_3_3 11 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  85 142 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 85 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 85 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 142 (accept_3_3 8 85 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 85 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 142
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 85 142 (accept_3_3 5 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85
  142 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 85 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 85 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 85 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 142 (accept_3_3 2 85 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 85 142 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 85 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  142)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 84 142 (Eq.refl Bool.true)
  (allA_succ_of_gcd 58 84 142 2 29 42 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 84 142 (Polychromatic418967fa.accept_10_7_4_2_1_903 57 84 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 84 142 2 28 42 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 84 142 (Polychromatic418967fa.accept_9_1_3_7_1_6 55 84
  142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 84 142 2 27 42 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 84 142 (accept_3_3 53
  84 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 84 142 2 26 42 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 84 142
  (Polychromatic418967fa.accept_9_6_3_7_1_580 51 84 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 84 142 2 25 42 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 84 142 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 84 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 84 142 2 24 42 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 84 142 (accept_3_3 47 84 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 84 142 2 23 42 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 84 142 (Polychromatic418967fa.accept_18_9_12_16_1_7323 45 84
  142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 84 142 2 22 42 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 84 142
  (Polychromatic418967fa.accept_15_13_9_7_1_2194 43 84 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 84 142 2 21 42 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 84 142 (accept_3_3 41 84 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 84
  142 2 20 42 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  84 142 (Polychromatic418967fa.accept_16_7_4_14_1_2860 39 84 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 84 142 2 19 42 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 84 142 (Polychromatic418967fa.accept_9_1_3_7_1_6 37 84 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 84 142 2 18 42 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 84 142 (accept_3_3 35 84 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 84 142 2 17 42 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 84 142
  (Polychromatic418967fa.accept_9_6_3_7_1_580 33 84 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 84 142 2 16 42 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 84 142 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 84 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84 142 2 15 42 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 84 142 (accept_3_3 29 84 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 84 142 2 14 42 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 84 142 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 84 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 84 142 2 13 42 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 84 142
  (Polychromatic418967fa.accept_11_3_7_10_1_180 25 84 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 84 142 2 12 42 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 84 142 (accept_3_3 23 84 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 84
  142 2 11 42 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  84 142 (Polychromatic418967fa.accept_22_21_18_10_1_5757 21 84 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 84 142 2 10 42 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 84 142 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 84 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84 142 2 9 42 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 84 142 (accept_3_3 17 84 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 84 142 2 8 42 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 84 142 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 84 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 84 142 2 7 42 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 142
  (Polychromatic418967fa.accept_9_4_3_7_1_296 13 84 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 84 142 2 6 42 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 84 142 (accept_3_3 11 84 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84
  142 2 5 42 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  84 142 (Polychromatic418967fa.accept_16_9_4_14_1_1878 9 84 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 84 142 2 4 42 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 84 142 (Polychromatic418967fa.accept_10_7_4_2_1_903 7 84 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 142 2 3 42 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 142 (accept_3_3 5 84 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 84 142 2 2 42 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 84 142 (Polychromatic418967fa.accept_11_3_7_10_1_180 3 84 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 84 142 2 1 42 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 142
  (Polychromatic418967fa.accept_9_1_3_7_1_6 1 84 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 84 142))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 83 142 (Eq.refl Bool.true)
  (allA_of_3_1 60 83 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 61 82 142 (Eq.refl Bool.true)
  (allA_succ_of_gcd 60 82 142 2 30 41 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 82 142 (accept_3_3 59 82 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 82
  142 2 29 41 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57
  82 142 (Polychromatic418967fa.accept_9_3_1_7_1_97 57 82 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 82 142 2 28 41 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 82 142 (Polychromatic418967fa.accept_13_3_4_12_1_36 55 82 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 82 142 2 27 41 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 82 142 (accept_3_3 53 82 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 82 142 2 26 41 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 82 142
  (Polychromatic418967fa.accept_9_6_1_7_1_577 51 82 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 82 142 2 25 41 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 82 142 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 82 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 82 142 2 24 41 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 82 142 (accept_3_3 47 82 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 82 142 2 23 41 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 82 142 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 82 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 82 142 2 22 41 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 82 142
  (Polychromatic418967fa.accept_21_1_19_16_1_2901 43 82 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 82 142 2 21 41 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 82 142 (accept_3_3 41 82 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 82
  142 2 20 41 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  82 142 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 82 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 82 142 2 19 41 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 82 142 (Polychromatic418967fa.accept_11_4_5_10_1_926 37 82 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 82 142 2 18 41 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 82 142 (accept_3_3 35 82 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 82 142 2 17 41 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 82 142
  (Polychromatic418967fa.accept_9_6_1_7_1_577 33 82 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 82 142 2 16 41 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 82 142 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 82 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 82 142 2 15 41 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 82 142 (accept_3_3 29 82 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 82 142 2 14 41 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 82 142 (Polychromatic418967fa.accept_22_5_16_10_1_7349 27 82
  142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 82 142 2 13 41 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 82 142
  (Polychromatic418967fa.accept_7_4_5_2_1_243 25 82 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 82 142 2 12 41 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 82 142 (accept_3_3 23 82 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 82
  142 2 11 41 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  82 142 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 82 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 82 142 2 10 41 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 82 142 (Polychromatic418967fa.accept_18_1_10_16_1_566 19 82 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 82 142 2 9 41 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 82 142 (accept_3_3 17 82 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 82 142 2 8 41 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 82 142 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 82 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 82 142 2 7 41 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 82 142
  (Polychromatic418967fa.accept_9_4_1_7_1_293 13 82 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 82 142 2 6 41 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 82 142 (accept_3_3 11 82 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 82
  142 2 5 41 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  82 142 (Polychromatic418967fa.accept_23_9_13_4_1_7348 9 82 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 82 142 2 4 41 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 82 142 (Polychromatic418967fa.accept_13_7_4_12_1_1341 7 82 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 82 142 2 3 41 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 82 142 (accept_3_3 5 82 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 82 142 2 2 41 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 82 142 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 82 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 82 142 2 1 41 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 82 142
  (Polychromatic418967fa.accept_18_1_10_16_1_566 1 82 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 82 142))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 81 142 (Eq.refl
  Bool.true) (allA_succ_of_accept 61 81 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 81 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 81 142 (Polychromatic418967fa.accept_11_5_4_10_1_524
  60 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 142 (accept_3_3 59
  81 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 142
  (Polychromatic418967fa.accept_15_13_6_7_1_1369 58 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 81 142 (Polychromatic418967fa.accept_15_12_6_7_1_1353 57 81 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 81 142 (accept_3_3 56 81 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 81 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 81 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 81 142 (Polychromatic418967fa.accept_7_5_4_2_1_235 54
  81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 142 (accept_3_3 53 81
  142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 142
  (Polychromatic418967fa.accept_16_4_1_14_1_3908 52 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 81 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 81 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 81 142 (accept_3_3 50 81 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 81 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 81 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 81 142 (Polychromatic418967fa.accept_7_6_4_2_1_236 48
  81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 142 (accept_3_3 47 81
  142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 142
  (Polychromatic418967fa.accept_10_6_1_2_1_874 46 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 81 142 (Polychromatic418967fa.accept_16_13_1_14_1_2855 45 81 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 81 142 (accept_3_3 44 81 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 81 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 81 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 81 142 (Polychromatic418967fa.accept_12_6_9_10_1_565
  42 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 142 (accept_3_3 41
  81 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 142
  (Polychromatic418967fa.accept_7_5_4_2_1_235 40 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 81 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 81 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 81 142 (accept_3_3 38 81 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 81 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 81 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 81 142 (Polychromatic418967fa.accept_10_6_1_2_1_874
  36 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 142 (accept_3_3 35
  81 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 142
  (Polychromatic418967fa.accept_7_6_4_2_1_236 34 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 81 142 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 81 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 81 142 (accept_3_3 32 81 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 81 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 81 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 81 142 (Polychromatic418967fa.accept_12_6_9_10_1_565
  30 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 142 (accept_3_3 29
  81 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 142
  (Polychromatic418967fa.accept_13_2_3_12_1_735 28 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 81 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 81 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 81 142 (accept_3_3 26 81 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 81 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 81 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 81 142 (Polychromatic418967fa.accept_17_7_13_6_1_811
  24 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 142 (accept_3_3 23
  81 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 142
  (Polychromatic418967fa.accept_13_9_3_12_1_2025 22 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 81 142 (Polychromatic418967fa.accept_24_21_9_22_1_7347 21 81 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 81 142 (accept_3_3 20 81 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 81 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 81 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 81 142 (Polychromatic418967fa.accept_12_6_9_10_1_565
  18 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 142 (accept_3_3 17
  81 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 142
  (Polychromatic418967fa.accept_10_6_1_2_1_874 16 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 81 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 81 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 81 142 (accept_3_3 14 81 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 81 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 81 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 81 142 (Polychromatic418967fa.accept_7_5_4_2_1_235 12
  81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 142 (accept_3_3 11 81
  142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 142
  (Polychromatic418967fa.accept_25_10_6_17_1_7346 10 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 81 142 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 81 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 81 142 (accept_3_3 8 81 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 81 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 81 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 142 (Polychromatic418967fa.accept_7_6_4_2_1_236 6
  81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 142 (accept_3_3 5 81 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 142 (Polychromatic418967fa.accept_13_4_3_12_1_2066
  4 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 142
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 81 142 (accept_3_3 2 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81
  142 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 81 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 81 142)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 80 142 (Eq.refl
  Bool.true) (allA_of_3_1 63 80 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 64 79 142 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 79 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 79 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 79 142 (accept_3_3 62 79 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 79 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 79 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 79 142 (Polychromatic418967fa.accept_13_8_1_12_1_762
  60 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 79 142 (accept_3_3 59
  79 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 79 142
  (Polychromatic418967fa.accept_16_10_15_14_1_1086 58 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 79 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 79 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 79 142 (accept_3_3 56 79 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 79 142 (Polychromatic418967fa.accept_15_10_4_7_1_3127 55 79 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 79 142
  (Polychromatic418967fa.accept_13_2_1_12_1_1326 54 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 79 142 (accept_3_3 53 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  79 142 (Polychromatic418967fa.accept_12_4_7_10_1_563 52 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 79 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 79 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 79 142 (accept_3_3 50 79 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 79 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 79 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 79 142
  (Polychromatic418967fa.accept_15_3_4_7_1_1352 48 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 79 142 (accept_3_3 47 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  79 142 (Polychromatic418967fa.accept_14_4_9_2_1_95 46 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 79 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 79 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 79 142 (accept_3_3 44 79 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 79 142 (Polychromatic418967fa.accept_20_3_19_2_1_5926 43 79 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 79 142
  (Polychromatic418967fa.accept_15_12_4_7_1_3097 42 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 79 142 (accept_3_3 41 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  79 142 (Polychromatic418967fa.accept_12_4_7_10_1_563 40 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 79 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 79 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 79 142 (accept_3_3 38 79 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 79 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 79 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 79 142
  (Polychromatic418967fa.accept_16_4_15_14_1_5056 36 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 79 142 (accept_3_3 35 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  79 142 (Polychromatic418967fa.accept_11_1_2_10_1_1426 34 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 79 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 79 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 79 142 (accept_3_3 32 79 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 79 142 (Polychromatic418967fa.accept_10_1_9_2_1_45 31 79 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 79 142
  (Polychromatic418967fa.accept_17_13_11_6_1_4837 30 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 79 142 (accept_3_3 29 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  79 142 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 79 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 79 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 142 (accept_3_3 26 79 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 79 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 79 142
  (Polychromatic418967fa.accept_13_11_1_12_1_742 24 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 79 142 (accept_3_3 23 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  79 142 (Polychromatic418967fa.accept_17_5_11_6_1_4815 22 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 79 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 79 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 142 (accept_3_3 20 79 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 142 (Polychromatic418967fa.accept_18_1_7_16_1_1342 19 79 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 142
  (Polychromatic418967fa.accept_13_5_1_12_1_740 18 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 79 142 (accept_3_3 17 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  79 142 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 79 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 79 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 142 (accept_3_3 14 79 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 79 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 142
  (Polychromatic418967fa.accept_11_1_2_10_1_1426 12 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 142 (accept_3_3 11 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  79 142 (Polychromatic418967fa.accept_15_10_4_7_1_3127 10 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 79 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 79 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 142 (accept_3_3 8 79 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 142 (Polychromatic418967fa.accept_10_7_9_2_1_1887 7 79 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 142
  (Polychromatic418967fa.accept_19_6_3_9_1_3332 6 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 142 (accept_3_3 5 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  142 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 79 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 79 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 79 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 142 (accept_3_3 2 79 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 79 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 79 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79
  142)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 78 142 (Eq.refl Bool.true)
  (allA_succ_of_gcd 64 78 142 2 32 39 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 78 142 (Polychromatic418967fa.accept_12_3_6_10_1_576 63 78 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 78 142 2 31 39 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 78 142 (Polychromatic418967fa.accept_19_4_2_9_1_4584
  61 78 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 78 142 2 30 39 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 78 142 (accept_3_3 59
  78 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 78 142 2 29 39 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 78 142
  (Polychromatic418967fa.accept_9_3_6_7_1_562 57 78 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 78 142 2 28 39 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 78 142 (Polychromatic418967fa.accept_7_6_1_2_1_230 55 78 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 78 142 2 27 39 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 78 142 (accept_3_3 53 78 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 78 142 2 26 39 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 78 142 (Polychromatic418967fa.accept_12_3_6_10_1_576 51 78 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 78 142 2 25 39 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 78 142
  (Polychromatic418967fa.accept_9_4_6_7_1_286 49 78 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 78 142 2 24 39 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 78 142 (accept_3_3 47 78 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 78
  142 2 23 39 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  78 142 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 78 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 78 142 2 22 39 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 78 142 (Polychromatic418967fa.accept_14_1_8_2_1_1675 43 78 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 78 142 2 21 39 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 78 142 (accept_3_3 41 78 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 78 142 2 20 39 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 78 142
  (Polychromatic418967fa.accept_9_3_6_7_1_562 39 78 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 78 142 2 19 39 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 78 142 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 78 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78 142 2 18 39 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 78 142 (accept_3_3 35 78 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 78 142 2 17 39 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 78 142 (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 78 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 78 142 2 16 39 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 78 142
  (Polychromatic418967fa.accept_7_3_1_2_1_247 31 78 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 78 142 2 15 39 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 78 142 (accept_3_3 29 78 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 78
  142 2 14 39 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  78 142 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 78 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 78 142 2 13 39 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 78 142 (Polychromatic418967fa.accept_10_5_8_2_1_517 25 78 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 78 142 2 12 39 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 78 142 (accept_3_3 23 78 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 78 142 2 11 39 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 78 142
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 78 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 78 142 2 10 39 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 78 142 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 78 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 142 2 9 39 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 142 (accept_3_3 17 78 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 78 142 2 8 39 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 78 142 (Polychromatic418967fa.accept_10_5_8_2_1_517 15 78 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 78 142 2 7 39 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 78 142 (Polychromatic418967fa.accept_7_6_1_2_1_230 13
  78 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 142 2 6 39 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 142 (accept_3_3 11
  78 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 78 142 2 5 39 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 78 142
  (Polychromatic418967fa.accept_11_9_1_10_1_920 9 78 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 78 142 2 4 39 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 78 142 (Polychromatic418967fa.accept_19_7_2_9_1_6006 7 78 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 142 2 3 39 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 142 (accept_3_3 5 78 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 78 142 2 2 39 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 78 142 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 78 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 78 142 2 1 39 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 142 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 78
  142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  142))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 77 142 (Eq.refl Bool.true)
  (allA_of_3_1 66 77 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 67 76 142 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 76 142 2 33 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 76 142 (accept_3_3 65 76 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 76
  142 2 32 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63
  76 142 (Polychromatic418967fa.accept_25_13_1_17_1_7345 63 76 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 76 142 2 31 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 76 142 (Polychromatic418967fa.accept_10_1_6_2_1_867 61 76 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 76 142 2 30 38 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 76 142 (accept_3_3 59 76 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 76 142 2 29 38 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 76 142
  (Polychromatic418967fa.accept_7_1_6_2_1_18 57 76 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 76 142 2 28 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 76 142 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 76 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 76 142 2 27 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 76 142 (accept_3_3 53 76 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 76 142 2 26 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 76 142 (Polychromatic418967fa.accept_9_6_4_7_1_300 51 76 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 76 142 2 25 38 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 76 142
  (Polychromatic418967fa.accept_12_1_4_10_1_209 49 76 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 76 142 2 24 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 76 142 (accept_3_3 47 76 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 76
  142 2 23 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  76 142 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 76 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 76 142 2 22 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 76 142 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 76 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 76 142 2 21 38 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 76 142 (accept_3_3 41 76 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 76 142 2 20 38 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 76 142
  (Polychromatic418967fa.accept_7_4_6_2_1_451 39 76 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 76 142 2 19 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 76 142 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 76 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 76 142 2 18 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 76 142 (accept_3_3 35 76 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 76 142 2 17 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 76 142 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 76 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 76 142 2 16 38 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 76 142
  (Polychromatic418967fa.accept_7_3_6_2_1_90 31 76 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 76 142 2 15 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 76 142 (accept_3_3 29 76 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 76
  142 2 14 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  76 142 (Polychromatic418967fa.accept_13_1_11_12_1_1322 27 76 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 76 142 2 13 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 76 142 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 76 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 76 142 2 12 38 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 76 142 (accept_3_3 23 76 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 76 142 2 11 38 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 76 142
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 76 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 76 142 2 10 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 76 142 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 76 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 76 142 2 9 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 76 142 (accept_3_3 17 76 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 76 142 2 8 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 76 142 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 76 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 76 142 2 7 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 76 142 (Polychromatic418967fa.accept_12_1_4_10_1_209
  13 76 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 76 142 2 6 38 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 76 142 (accept_3_3 11
  76 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 76 142 2 5 38 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 76 142
  (Polychromatic418967fa.accept_15_9_1_7_1_1350 9 76 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 76 142 2 4 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 76 142 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 76 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 76 142 2 3 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 76 142 (accept_3_3 5 76 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 76 142 2 2 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 76 142 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 76 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 76 142 2 1 38 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 76 142 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 76
  142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76
  142))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 75 142 (Eq.refl Bool.true)
  (allA_succ_of_accept 67 75 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 75 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 75 142 (Polychromatic418967fa.accept_7_3_5_2_1_17 66 75 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 75 142 (accept_3_3 65 75 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 142 (Polychromatic418967fa.accept_9_1_3_7_1_6 64
  75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 142
  (Polychromatic418967fa.accept_10_3_5_2_1_38 63 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 75 142 (accept_3_3 62 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  75 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 75 142 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 75 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 75 142 (accept_3_3 59 75 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 142 (Polychromatic418967fa.accept_9_4_3_7_1_296 58 75 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 142
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 75 142 (accept_3_3 56 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  75 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 75 142 (Polychromatic418967fa.accept_12_6_3_10_1_224 54 75 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 75 142 (accept_3_3 53 75 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 142 (Polychromatic418967fa.accept_7_3_5_2_1_17 52 75 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 142
  (Polychromatic418967fa.accept_9_6_3_7_1_580 51 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 75 142 (accept_3_3 50 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  75 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 75 142 (Polychromatic418967fa.accept_10_8_5_2_1_881 48 75 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 75 142 (accept_3_3 47 75 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 142 (Polychromatic418967fa.accept_7_4_5_2_1_243 46 75 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 142
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 75 142 (accept_3_3 44 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  75 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 75 142 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 75 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 75 142 (accept_3_3 41 75 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 142 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 75 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 142
  (Polychromatic418967fa.accept_7_4_5_2_1_243 39 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 75 142 (accept_3_3 38 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  75 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 75 142 (Polychromatic418967fa.accept_27_9_21_7_1_7344 36 75 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 75 142 (accept_3_3 35 75 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 142 (Polychromatic418967fa.accept_11_1_9_10_1_184 34 75 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 142
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 75 142 (accept_3_3 32 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  75 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 75 142 (Polychromatic418967fa.accept_11_8_9_10_1_503 30 75 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 75 142 (accept_3_3 29 75 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 142 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 75 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 142
  (Polychromatic418967fa.accept_10_7_5_2_1_880 27 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 75 142 (accept_3_3 26 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  75 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 75 142 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 75 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 75 142 (accept_3_3 23 75 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 142 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 75 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 142
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 75 142 (accept_3_3 20 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  75 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 75 142 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 75 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 142 (accept_3_3 17 75 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 142 (Polychromatic418967fa.accept_17_16_7_6_1_7343 16 75 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 142
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 75 142 (accept_3_3 14 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  75 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 75 142 (Polychromatic418967fa.accept_11_1_9_10_1_184 12 75 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 142 (accept_3_3 11 75 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 142 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 75 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 142
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 75 142 (accept_3_3 8 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75
  142 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 75 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 75 142 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 75 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 75 142 (accept_3_3 5 75 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 75 142 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 75 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 75 142 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 75
  142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 142 (accept_3_3 2 75 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 75
  142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  142)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 74 142 (Eq.refl Bool.true)
  (allA_of_3_1 69 74 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 70 73 142 (Eq.refl Bool.true)
  (allA_succ_of_accept 69 73 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 73 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 142 (accept_3_3 68 73 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 73 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 73 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 142 (Polychromatic418967fa.accept_9_3_1_7_1_97 66
  73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 73 142 (accept_3_3 65 73
  142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 73 142 (Polychromatic418967fa.accept_7_1_3_2_1_13
  64 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 73 142
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 73 142 (accept_3_3 62 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  73 142 (Polychromatic418967fa.accept_7_5_3_2_1_249 61 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 73 142 (Polychromatic418967fa.accept_9_6_1_7_1_577 60 73 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 73 142 (accept_3_3 59 73 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 73 142 (Polychromatic418967fa.accept_9_4_1_7_1_293 58 73 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 73 142
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 73 142 (accept_3_3 56 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  73 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 73 142 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 73 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 73 142 (accept_3_3 53 73 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 73 142 (Polychromatic418967fa.accept_12_4_1_10_1_221 52 73 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 73 142
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 73 142 (accept_3_3 50 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  73 142 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 73 142 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 73 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 73 142 (accept_3_3 47 73 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 73 142 (Polychromatic418967fa.accept_13_7_8_12_1_2810 46 73 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 73 142
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 73 142 (accept_3_3 44 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  73 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 73 142 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 73 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 73 142 (accept_3_3 41 73 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 73 142 (Polychromatic418967fa.accept_7_5_3_2_1_249 40 73 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 73 142
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 73 142 (accept_3_3 38 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  73 142 (Polychromatic418967fa.accept_16_5_9_14_1_5051 37 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 73 142 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 73 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 73 142 (accept_3_3 35 73 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 73 142 (Polychromatic418967fa.accept_7_6_3_2_1_461 34 73 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 73 142
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 73 142 (accept_3_3 32 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  73 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 73 142 (Polychromatic418967fa.accept_9_3_1_7_1_97 30 73 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 73 142 (accept_3_3 29 73 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 73 142 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 73 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 73 142
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 73 142 (accept_3_3 26 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  73 142 (Polychromatic418967fa.accept_10_5_3_2_1_899 25 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 73 142 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 73 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 73 142 (accept_3_3 23 73 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 73 142 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 73 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 73 142
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 73 142 (accept_3_3 20 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  73 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 73 142 (Polychromatic418967fa.accept_13_5_8_12_1_2759 18 73 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 73 142 (accept_3_3 17 73 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 73 142 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 73 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 73 142
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 73 142 (accept_3_3 14 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  73 142 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 73 142 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 73 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 73 142 (accept_3_3 11 73 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 73 142 (Polychromatic418967fa.accept_13_10_8_12_1_2032 10 73 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 73 142
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 73 142 (accept_3_3 8 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 73
  142 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 73 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 73 142 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 73 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 73 142 (accept_3_3 5 73 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 73 142 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 73 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 73 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 73
  142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 142 (accept_3_3 2 73 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 73 142 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 73
  142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  142)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 72 142 (Eq.refl Bool.true)
  (allA_succ_of_gcd 70 72 142 2 35 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 72 142 (Polychromatic418967fa.accept_13_4_7_12_1_2823 69 72 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 72 142 2 34 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 72 142 (Polychromatic418967fa.accept_19_10_15_9_1_396
  67 72 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 142 2 33 36 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 142 (accept_3_3 65
  72 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 72 142 2 32 36 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 72 142
  (Polychromatic418967fa.accept_13_11_7_12_1_2758 63 72 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 72 142 2 31 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 72 142 (Polychromatic418967fa.accept_17_10_4_6_1_3757 61 72 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 72 142 2 30 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 72 142 (accept_3_3 59 72 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 58 72 142 2 29 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 72 142 (Polychromatic418967fa.accept_13_5_7_12_1_2757 57 72 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 72 142 2 28 36 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 72 142
  (Polychromatic418967fa.accept_15_10_12_7_1_1358 55 72 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 72 142 2 27 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 72 142 (accept_3_3 53 72 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 72
  142 2 26 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  72 142 (Polychromatic418967fa.accept_15_6_12_7_1_1360 51 72 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 72 142 2 25 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 72 142 (Polychromatic418967fa.accept_11_5_6_10_1_1432 49 72 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 142 2 24 36 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 142 (accept_3_3 47 72 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 72 142 2 23 36 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 72 142
  (Polychromatic418967fa.accept_13_6_7_12_1_3504 45 72 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 72 142 2 22 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 72 142 (Polychromatic418967fa.accept_13_4_7_12_1_2823 43 72 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72 142 2 21 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 72 142 (accept_3_3 41 72 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 72 142 2 20 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 72 142 (Polychromatic418967fa.accept_17_5_4_6_1_7342 39 72 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 72 142 2 19 36 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 72 142
  (Polychromatic418967fa.accept_13_11_7_12_1_2758 37 72 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 72 142 2 18 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 72 142 (accept_3_3 35 72 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 72
  142 2 17 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  72 142 (Polychromatic418967fa.accept_15_3_12_7_1_1346 33 72 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 72 142 2 16 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 72 142 (Polychromatic418967fa.accept_13_5_7_12_1_2757 31 72 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 142 2 15 36 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 142 (accept_3_3 29 72 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 72 142 2 14 36 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 72 142
  (Polychromatic418967fa.accept_11_5_6_10_1_1432 27 72 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 72 142 2 13 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 72 142 (Polychromatic418967fa.accept_15_10_12_7_1_1358 25 72 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 142 2 12 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 142 (accept_3_3 23 72 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72 142 2 11 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 72 142 (Polychromatic418967fa.accept_13_8_7_12_1_3637 21 72 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 72 142 2 10 36 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 72 142
  (Polychromatic418967fa.accept_13_6_7_12_1_3504 19 72 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 72 142 2 9 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 72 142 (accept_3_3 17 72 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 72
  142 2 8 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  72 142 (Polychromatic418967fa.accept_21_15_9_16_1_7341 15 72 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 72 142 2 7 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 72 142 (Polychromatic418967fa.accept_19_13_15_9_1_3293 13 72 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 142 2 6 36 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 142 (accept_3_3 11 72 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72 142 2 5 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 72 142 (Polychromatic418967fa.accept_20_9_12_2_1_5935 9 72 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 72 142 2 4 36 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 72 142
  (Polychromatic418967fa.accept_20_7_12_2_1_4465 7 72 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 72 142 2 3 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 72 142 (accept_3_3 5 72 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 72 142
  2 2 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 72
  142 (Polychromatic418967fa.accept_15_3_12_7_1_1346 3 72 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 72 142 2 1 36 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 72 142 (Polychromatic418967fa.accept_23_1_3_4_1_7340 1 72 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72
  142))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 142 (allA_of_3_1 71 71 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 70 142 (allA_succ_of_accept 69 70 142
  (Polychromatic418967fa.accept_13_4_5_12_1_751 69 70 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 70 142 2 34 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 70 142 (Polychromatic418967fa.accept_13_2_5_12_1_2043 67 70 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 70 142 2 33 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 70 142 (accept_3_3 65 70 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 64 70 142 2 32 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 70 142 (Polychromatic418967fa.accept_15_3_10_7_1_2196 63 70 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 70 142 2 31 35 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 70 142
  (Polychromatic418967fa.accept_15_1_10_7_1_4087 61 70 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 70 142 2 30 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 70 142 (accept_3_3 59 70 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 70
  142 2 29 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57
  70 142 (Polychromatic418967fa.accept_15_12_10_7_1_1357 57 70 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 70 142 2 28 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 70 142 (Polychromatic418967fa.accept_17_4_2_6_1_2629 55 70 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 70 142 2 27 35 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 70 142 (accept_3_3 53 70 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 70 142 2 26 35 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 70 142
  (Polychromatic418967fa.accept_21_9_7_16_1_5904 51 70 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 70 142 2 25 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 70 142 (Polychromatic418967fa.accept_11_5_4_10_1_524 49 70 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 70 142 2 24 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 70 142 (accept_3_3 47 70 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 70 142 2 23 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 70 142 (Polychromatic418967fa.accept_13_6_5_12_1_307 45 70 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 70 142 2 22 35 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 70 142
  (Polychromatic418967fa.accept_13_4_5_12_1_751 43 70 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 70 142 2 21 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 70 142 (accept_3_3 41 70 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 70
  142 2 20 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  70 142 (Polychromatic418967fa.accept_22_17_4_10_1_7339 39 70 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 70 142 2 19 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 70 142 (Polychromatic418967fa.accept_19_18_13_9_1_5971 37 70 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 70 142 2 18 35 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 70 142 (accept_3_3 35 70 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 70 142 2 17 35 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 70 142
  (Polychromatic418967fa.accept_13_7_5_12_1_1305 33 70 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 70 142 2 16 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 70 142 (Polychromatic418967fa.accept_15_1_10_7_1_4087 31 70 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 70 142 2 15 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 70 142 (accept_3_3 29 70 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 70 142 2 14 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 70 142 (Polychromatic418967fa.accept_11_5_4_10_1_524 27 70 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 70 142 2 13 35 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 70 142
  (Polychromatic418967fa.accept_19_6_13_9_1_3291 25 70 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 70 142 2 12 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 70 142 (accept_3_3 23 70 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 70
  142 2 11 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  70 142 (Polychromatic418967fa.accept_13_8_5_12_1_2755 21 70 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 70 142 2 10 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 70 142 (Polychromatic418967fa.accept_13_6_5_12_1_307 19 70 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 70 142 2 9 35 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 70 142 (accept_3_3 17 70 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 70 142 2 8 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 70 142 (Polychromatic418967fa.accept_13_2_5_12_1_2043 15 70 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 70 142 2 7 35 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 70 142
  (Polychromatic418967fa.accept_17_13_2_6_1_3683 13 70 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 70 142 2 6 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 70 142 (accept_3_3 11 70 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70
  142 2 5 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  70 142 (Polychromatic418967fa.accept_21_9_7_16_1_5904 9 70 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 70 142 2 4 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 70 142 (Polychromatic418967fa.accept_13_7_5_12_1_1305 7 70 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 70 142 2 3 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 70 142 (accept_3_3 5 70 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 70 142 2 2 35 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 70 142 (Polychromatic418967fa.accept_15_3_10_7_1_2196 3 70 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 70 142 2 1 35 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 70 142
  (Polychromatic418967fa.accept_13_1_5_12_1_306 1 70 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 70 142)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 142
  (allA_succ_of_accept 68 69 142 (accept_3_3 68 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  69 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 69 142 (Polychromatic418967fa.accept_7_3_6_2_1_90 66 69 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 69 142 (accept_3_3 65 69 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 142 (Polychromatic418967fa.accept_7_1_6_2_1_18 64 69 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 142
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 69 142 (accept_3_3 62 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  69 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 69 142 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 69 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 69 142 (accept_3_3 59 69 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 142 (Polychromatic418967fa.accept_9_4_6_7_1_286 58 69 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 142
  (Polychromatic418967fa.accept_7_1_6_2_1_18 57 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 69 142 (accept_3_3 56 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  69 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 69 142 (Polychromatic418967fa.accept_12_6_9_10_1_565 54 69 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 69 142 (accept_3_3 53 69 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 142 (Polychromatic418967fa.accept_7_3_6_2_1_90 52 69 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 142
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 69 142 (accept_3_3 50 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  69 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 69 142 (Polychromatic418967fa.accept_9_3_6_7_1_562 48 69 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 69 142 (accept_3_3 47 69 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 142 (Polychromatic418967fa.accept_7_4_6_2_1_451 46 69 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 142
  (Polychromatic418967fa.accept_7_3_6_2_1_90 45 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 69 142 (accept_3_3 44 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  69 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 69 142 (Polychromatic418967fa.accept_12_6_9_10_1_565 42 69 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 69 142 (accept_3_3 41 69 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 142 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 69 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 142
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 69 142 (accept_3_3 38 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  69 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 69 142 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 69 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 69 142 (accept_3_3 35 69 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 142 (Polychromatic418967fa.accept_13_8_4_12_1_2753 34 69 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 142
  (Polychromatic418967fa.accept_13_7_4_12_1_1341 33 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 69 142 (accept_3_3 32 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  69 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 69 142 (Polychromatic418967fa.accept_9_3_6_7_1_562 30 69 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 142 (accept_3_3 29 69 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 142 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 69 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 142
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 69 142 (accept_3_3 26 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  69 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 69 142 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 69 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 142 (accept_3_3 23 69 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 142 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 69 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 142
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 69 142 (accept_3_3 20 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  69 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 69 142 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 69 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 142 (accept_3_3 17 69 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 142 (Polychromatic418967fa.accept_13_3_4_12_1_36 16 69 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 142
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 69 142 (accept_3_3 14 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  69 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 69 142 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 69 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 142 (accept_3_3 11 69 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 142 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 69 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 142
  (Polychromatic418967fa.accept_16_9_5_14_1_6126 9 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 69 142 (accept_3_3 8 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69
  142 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 69 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 69 142 (Polychromatic418967fa.accept_12_6_9_10_1_565 6 69 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 142 (accept_3_3 5 69 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 69 142 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 69 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 69
  142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 142 (accept_3_3 2 69 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 69
  142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  142))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 142 (allA_of_3_1 68 68 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 67 142 (allA_succ_of_accept 66 67 142
  (Polychromatic418967fa.accept_9_3_4_7_1_89 66 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 142 (accept_3_3 65 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 142 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 67 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 142 (accept_3_3 62 67 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 67 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 142
  (Polychromatic418967fa.accept_9_6_4_7_1_300 60 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 142 (accept_3_3 59 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 142 (Polychromatic418967fa.accept_13_6_2_12_1_2802 58 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 67 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 142 (accept_3_3 56 67 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 142 (Polychromatic418967fa.accept_7_6_4_2_1_236 55 67 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 142
  (Polychromatic418967fa.accept_7_5_4_2_1_235 54 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 142 (accept_3_3 53 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 142 (Polychromatic418967fa.accept_12_4_7_10_1_563 52 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 67 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 142 (accept_3_3 50 67 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 67 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 142
  (Polychromatic418967fa.accept_7_6_4_2_1_236 48 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 142 (accept_3_3 47 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 142 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 67 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 142 (accept_3_3 44 67 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 142 (Polychromatic418967fa.accept_13_4_2_12_1_2800 43 67 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 142
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 142 (accept_3_3 41 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 142 (Polychromatic418967fa.accept_7_5_4_2_1_235 40 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 67 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 142 (accept_3_3 38 67 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 67 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 142
  (Polychromatic418967fa.accept_13_10_2_12_1_1332 36 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 142 (accept_3_3 35 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 142 (Polychromatic418967fa.accept_7_6_4_2_1_236 34 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 67 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 142 (accept_3_3 32 67 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 142 (Polychromatic418967fa.accept_11_9_1_10_1_920 31 67 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 142
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 142 (accept_3_3 29 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 142 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 67 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 142 (accept_3_3 26 67 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 67 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 142
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 142 (accept_3_3 23 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 142 (Polychromatic418967fa.accept_19_3_10_9_1_7338 22 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 67 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 142 (accept_3_3 20 67 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 142 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 67 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 142
  (Polychromatic418967fa.accept_13_5_2_12_1_1301 18 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 142 (accept_3_3 17 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 142 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 67 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 142 (accept_3_3 14 67 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 67 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 142
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 142 (accept_3_3 11 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 142 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 67 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 142 (accept_3_3 8 67 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 142 (Polychromatic418967fa.accept_17_7_16_6_1_3705 7 67 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 142
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 142 (accept_3_3 5 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  142 (Polychromatic418967fa.accept_10_4_7_2_1_211 4 67 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 67 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 67 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 142 (accept_3_3 2 67 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 67 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 67 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  142))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 142 (allA_succ_of_accept 65 66
  142 (accept_3_3 65 66 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 66 142 2 32 33 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 66 142
  (Polychromatic418967fa.accept_12_3_6_10_1_576 63 66 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 66 142 2 31 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 66 142 (Polychromatic418967fa.accept_7_5_3_2_1_249 61 66 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 142 2 30 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 142 (accept_3_3 59 66 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 58 66 142 2 29 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 66 142 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 66 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 66 142 2 28 33 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 66 142
  (Polychromatic418967fa.accept_7_6_3_2_1_461 55 66 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 66 142 2 27 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 66 142 (accept_3_3 53 66 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 66
  142 2 26 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  66 142 (Polychromatic418967fa.accept_9_6_3_7_1_580 51 66 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 66 142 2 25 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 66 142 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 66 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 142 2 24 33 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 142 (accept_3_3 47 66 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 66 142 2 23 33 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 66 142
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 45 66 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 66 142 2 22 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 66 142 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 66 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 66 142 2 21 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 66 142 (accept_3_3 41 66 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 66 142 2 20 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 66 142 (Polychromatic418967fa.accept_12_3_6_10_1_576 39 66 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 66 142 2 19 33 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 66 142
  (Polychromatic418967fa.accept_9_1_3_7_1_6 37 66 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 66 142 2 18 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 66 142 (accept_3_3 35 66 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 66
  142 2 17 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  66 142 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 66 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 66 142 2 16 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 66 142 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 66 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 142 2 15 33 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 142 (accept_3_3 29 66 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 66 142 2 14 33 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 66 142
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 66 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 66 142 2 13 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 66 142 (Polychromatic418967fa.accept_17_8_15_6_1_4889 25 66 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 142 2 12 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 142 (accept_3_3 23 66 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 142 2 11 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 66 142 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 66 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 66 142 2 10 33 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 66 142
  (Polychromatic418967fa.accept_7_5_3_2_1_249 19 66 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 66 142 2 9 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 66 142 (accept_3_3 17 66 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66
  142 2 8 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  66 142 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 66 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 66 142 2 7 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 66 142 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 66 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 142 2 6 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 142 (accept_3_3 11 66 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 66 142 2 5 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 66 142 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 66 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 66 142 2 4 33 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 66 142
  (Polychromatic418967fa.accept_21_7_3_16_1_7337 7 66 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 66 142 2 3 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 66 142 (accept_3_3 5 66 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 142
  2 2 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 66
  142 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 66 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 66 142 2 1 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 66 142 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 66 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  142)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 142 (allA_of_3_1 65 65 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 64 142 (allA_succ_of_accept 63 64 142
  (Polychromatic418967fa.accept_11_8_9_10_1_503 63 64 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 64 142 2 31 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 64 142 (Polychromatic418967fa.accept_12_1_4_10_1_209 61 64 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 64 142 2 30 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 64 142 (accept_3_3 59 64 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 58 64 142 2 29 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 64 142 (Polychromatic418967fa.accept_9_3_1_7_1_97 57 64 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 64 142 2 28 32 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 64 142
  (Polychromatic418967fa.accept_7_6_1_2_1_230 55 64 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 64 142 2 27 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 64 142 (accept_3_3 53 64 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 64
  142 2 26 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  64 142 (Polychromatic418967fa.accept_9_6_1_7_1_577 51 64 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 64 142 2 25 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 64 142 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 64 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 64 142 2 24 32 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 64 142 (accept_3_3 47 64 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 64 142 2 23 32 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 64 142
  (Polychromatic418967fa.accept_7_3_1_2_1_247 45 64 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 64 142 2 22 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 64 142 (Polychromatic418967fa.accept_12_7_4_10_1_572 43 64 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 64 142 2 21 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 64 142 (accept_3_3 41 64 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 64 142 2 20 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 64 142 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 64 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 64 142 2 19 32 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 64 142
  (Polychromatic418967fa.accept_10_7_4_2_1_903 37 64 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 64 142 2 18 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 64 142 (accept_3_3 35 64 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 64
  142 2 17 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  64 142 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 64 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 64 142 2 16 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 64 142 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 64 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 64 142 2 15 32 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 64 142 (accept_3_3 29 64 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 64 142 2 14 32 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 64 142
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 64 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 64 142 2 13 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 64 142 (Polychromatic418967fa.accept_12_1_4_10_1_209 25 64 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 64 142 2 12 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 64 142 (accept_3_3 23 64 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 64 142 2 11 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 64 142 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 64 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 64 142 2 10 32 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 64 142
  (Polychromatic418967fa.accept_11_8_9_10_1_503 19 64 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 64 142 2 9 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 64 142 (accept_3_3 17 64 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 64
  142 2 8 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  64 142 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 64 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 64 142 2 7 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 64 142 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 64 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 64 142 2 6 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 64 142 (accept_3_3 11 64 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 64 142 2 5 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 64 142 (Polychromatic418967fa.accept_20_9_4_2_1_1900 9 64 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 64 142 2 4 32 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 64 142
  (Polychromatic418967fa.accept_10_7_4_2_1_903 7 64 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 64 142 2 3 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 64 142 (accept_3_3 5 64 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 64 142
  2 2 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 64
  142 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 64 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 64 142 2 1 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 64 142 (Polychromatic418967fa.accept_11_1_9_10_1_184 1 64 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 64 142))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 63 142 (allA_succ_of_accept 62 63 142 (accept_3_3 62 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 63 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 63 142 (Polychromatic418967fa.accept_19_3_6_9_1_7334 60 63 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 63 142 (accept_3_3 59 63 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 142
  (Polychromatic418967fa.accept_16_10_15_14_1_1086 58 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 63 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 63 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 142 (accept_3_3 56 63 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 63 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 63 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 63 142
  (Polychromatic418967fa.accept_12_6_3_10_1_224 54 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 63 142 (accept_3_3 53 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  63 142 (Polychromatic418967fa.accept_16_4_15_14_1_5056 52 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 63 142 (Polychromatic418967fa.accept_10_1_3_2_1_220 51 63 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 142 (accept_3_3 50 63 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 63 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 63 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 63 142
  (Polychromatic418967fa.accept_18_12_9_16_1_4732 48 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 63 142 (accept_3_3 47 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  63 142 (Polychromatic418967fa.accept_13_7_11_12_1_2051 46 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 63 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 63 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 142 (accept_3_3 44 63 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 63 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 63 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 63 142
  (Polychromatic418967fa.accept_11_9_8_10_1_934 42 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 63 142 (accept_3_3 41 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  63 142 (Polychromatic418967fa.accept_13_1_11_12_1_1322 40 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 63 142 (Polychromatic418967fa.accept_16_7_15_14_1_2889 39 63 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 142 (accept_3_3 38 63 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 63 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 63 142
  (Polychromatic418967fa.accept_13_10_11_12_1_1320 36 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 63 142 (accept_3_3 35 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 63 142 (Polychromatic418967fa.accept_15_4_3_7_1_713 34 63 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 63 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 142 (accept_3_3 32 63 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 31
  63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 63 142
  (Polychromatic418967fa.accept_12_6_3_10_1_224 30 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 63 142 (accept_3_3 29 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  63 142 (Polychromatic418967fa.accept_17_11_12_6_1_6070 28 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 63 142 (Polychromatic418967fa.accept_13_1_11_12_1_1322 27 63 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 142 (accept_3_3 26 63 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 63 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 63 142
  (Polychromatic418967fa.accept_25_24_13_17_1_7336 24 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 63 142 (accept_3_3 23 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 63 142 (Polychromatic418967fa.accept_19_3_6_9_1_7334 22 63 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 63 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 142 (accept_3_3 20 63 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 19
  63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 63 142
  (Polychromatic418967fa.accept_12_6_3_10_1_224 18 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 63 142 (accept_3_3 17 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  63 142 (Polychromatic418967fa.accept_19_16_6_9_1_7335 16 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 63 142 (Polychromatic418967fa.accept_10_5_3_2_1_899 15 63 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 142 (accept_3_3 14 63 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 63 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 63 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 63 142
  (Polychromatic418967fa.accept_14_12_7_2_1_1663 12 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 63 142 (accept_3_3 11 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  63 142 (Polychromatic418967fa.accept_13_10_11_12_1_1320 10 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 63 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 63 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 142 (accept_3_3 8 63 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 63 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 63 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63 142
  (Polychromatic418967fa.accept_12_6_3_10_1_224 6 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 142 (accept_3_3 5 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63
  142 (Polychromatic418967fa.accept_13_4_11_12_1_1318 4 63 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 63 142 (Polychromatic418967fa.accept_19_3_6_9_1_7334 3 63 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 142 (accept_3_3 2 63 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 63 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  142))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 142 (allA_of_3_1 62 62 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 61 142 (allA_succ_of_accept 60 61 142
  (Polychromatic418967fa.accept_7_4_5_2_1_243 60 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 142 (accept_3_3 59 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 142 (Polychromatic418967fa.accept_16_10_13_14_1_5042 58 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 61 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 142 (accept_3_3 56 61 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 61 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 142
  (Polychromatic418967fa.accept_15_9_1_7_1_1350 54 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 142 (accept_3_3 53 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 142 (Polychromatic418967fa.accept_7_3_5_2_1_17 52 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 61 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 142 (accept_3_3 50 61 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 142 (Polychromatic418967fa.accept_10_9_1_2_1_522 49 61 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 142
  (Polychromatic418967fa.accept_19_10_4_9_1_7333 48 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 142 (accept_3_3 47 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 142 (Polychromatic418967fa.accept_7_4_5_2_1_243 46 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 61 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 142 (accept_3_3 44 61 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 61 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 142
  (Polychromatic418967fa.accept_13_3_9_12_1_2062 42 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 142 (accept_3_3 41 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 142 (Polychromatic418967fa.accept_12_4_1_10_1_221 40 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 61 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 142 (accept_3_3 38 61 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 142 (Polychromatic418967fa.accept_18_1_7_16_1_1342 37 61 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 142
  (Polychromatic418967fa.accept_10_6_1_2_1_874 36 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 142 (accept_3_3 35 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 142 (Polychromatic418967fa.accept_13_8_9_12_1_2813 34 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 61 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 142 (accept_3_3 32 61 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 61 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 142
  (Polychromatic418967fa.accept_24_6_13_22_1_7332 30 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 142 (accept_3_3 29 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 142 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 61 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 142 (accept_3_3 26 61 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 142 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 61 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 142
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 142 (accept_3_3 23 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 142 (Polychromatic418967fa.accept_18_4_7_16_1_2307 22 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 61 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 142 (accept_3_3 20 61 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 61 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 142
  (Polychromatic418967fa.accept_7_4_5_2_1_243 18 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 142 (accept_3_3 17 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 142 (Polychromatic418967fa.accept_10_6_1_2_1_874 16 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 61 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 142 (accept_3_3 14 61 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 142 (Polychromatic418967fa.accept_10_3_1_2_1_521 13 61 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 142
  (Polychromatic418967fa.accept_17_12_10_6_1_3691 12 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 142 (accept_3_3 11 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 142 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 61 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 142 (accept_3_3 8 61 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 61 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 142
  (Polychromatic418967fa.accept_10_6_1_2_1_874 6 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 142 (accept_3_3 5 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  142 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 61 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 61 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 142 (accept_3_3 2 61 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 142 (Polychromatic418967fa.accept_16_1_13_14_1_1064 1 61 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 142)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 142 (allA_succ_of_accept 59 60 142 (accept_3_3 59 60 142 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 60 142 2 29 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 60 142 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 60 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 60 142 2 28 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 60 142 (Polychromatic418967fa.accept_7_6_4_2_1_236 55
  60 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 142 2 27 30 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 142 (accept_3_3 53
  60 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 60 142 2 26 30 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 60 142
  (Polychromatic418967fa.accept_14_9_4_2_1_983 51 60 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 60 142 2 25 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 60 142 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 60 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 60 142 2 24 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 60 142 (accept_3_3 47 60 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 60 142 2 23 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 60 142 (Polychromatic418967fa.accept_21_3_18_16_1_7331 45 60
  142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 60 142 2 22 30 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 60 142
  (Polychromatic418967fa.accept_13_4_8_12_1_3526 43 60 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 60 142 2 21 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 60 142 (accept_3_3 41 60 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 60
  142 2 20 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  60 142 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 60 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 60 142 2 19 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 60 142 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 60 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 142 2 18 30 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 60 142 (accept_3_3 35 60 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 60 142 2 17 30 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 60 142
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 60 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 60 142 2 16 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 60 142 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 60 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60 142 2 15 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 60 142 (accept_3_3 29 60 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 60 142 2 14 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 60 142 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 60 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 60 142 2 13 30 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 60 142
  (Polychromatic418967fa.accept_17_8_9_6_1_7330 25 60 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 60 142 2 12 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 60 142 (accept_3_3 23 60 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60
  142 2 11 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  60 142 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 60 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 60 142 2 10 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 60 142 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 60 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 142 2 9 30 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 60 142 (accept_3_3 17 60 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60 142 2 8 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 60 142 (Polychromatic418967fa.accept_11_4_5_10_1_926 15 60 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 60 142 2 7 30 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 60 142
  (Polychromatic418967fa.accept_7_6_4_2_1_236 13 60 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 60 142 2 6 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 60 142 (accept_3_3 11 60 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60
  142 2 5 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  60 142 (Polychromatic418967fa.accept_13_9_8_12_1_2031 9 60 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 60 142 2 4 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 60 142 (Polychromatic418967fa.accept_13_7_8_12_1_2810 7 60 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 142 2 3 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60 142 (accept_3_3 5 60 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 60 142 2 2 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 60 142 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 60 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 60 142 2 1 30 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 142
  (Polychromatic418967fa.accept_9_1_6_7_1_285 1 60 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 60 142)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 142 (allA_of_3_1 59 59 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 58 142 (allA_succ_of_accept 57 58 142
  (Polychromatic418967fa.accept_9_3_4_7_1_89 57 58 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 58 142 2 28 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 58 142 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 58 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 58 142 2 27 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 58 142 (accept_3_3 53 58 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 58 142 2 26 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 58 142 (Polychromatic418967fa.accept_9_6_4_7_1_300 51 58 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 58 142 2 25 29 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 58 142
  (Polychromatic418967fa.accept_13_10_6_12_1_2780 49 58 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 58 142 2 24 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 58 142 (accept_3_3 47 58 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 58
  142 2 23 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  58 142 (Polychromatic418967fa.accept_10_5_8_2_1_517 45 58 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 58 142 2 22 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 58 142 (Polychromatic418967fa.accept_18_7_4_16_1_2299 43 58 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 58 142 2 21 29 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 58 142 (accept_3_3 41 58 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 58 142 2 20 29 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 58 142
  (Polychromatic418967fa.accept_9_3_4_7_1_89 39 58 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 58 142 2 19 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 58 142 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 58 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 58 142 2 18 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 58 142 (accept_3_3 35 58 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 58 142 2 17 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 58 142 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 58 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 58 142 2 16 29 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 58 142
  (Polychromatic418967fa.accept_13_5_6_12_1_2750 31 58 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 58 142 2 15 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 58 142 (accept_3_3 29 58 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 58
  142 2 14 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  58 142 (Polychromatic418967fa.accept_19_8_1_9_1_7329 27 58 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 58 142 2 13 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 58 142 (Polychromatic418967fa.accept_10_5_8_2_1_517 25 58 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 58 142 2 12 29 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 58 142 (accept_3_3 23 58 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 58 142 2 11 29 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 58 142
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 58 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 58 142 2 10 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 58 142 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 58 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 58 142 2 9 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 58 142 (accept_3_3 17 58 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 58 142 2 8 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 58 142 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 58 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 58 142 2 7 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 58 142
  (Polychromatic418967fa.accept_16_13_10_14_1_2871 13 58 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 58 142 2 6 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 58 142 (accept_3_3 11 58 142 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 58 142 2 5 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 58 142 (Polychromatic418967fa.accept_15_9_13_7_1_1361 9 58 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 58 142 2 4 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 58 142 (Polychromatic418967fa.accept_11_7_3_10_1_1461 7 58 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 58 142 2 3 29 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 58 142 (accept_3_3 5 58 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 58 142 2 2 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 58 142 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 58
  142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 58 142 2 1 29 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 58 142
  (Polychromatic418967fa.accept_9_1_4_7_1_7 1 58 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 58 142)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 142 (allA_succ_of_accept 56
  57 142 (accept_3_3 56 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 142
  (Polychromatic418967fa.accept_4_3_1_2_1_62 55 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 57 142 (Polychromatic418967fa.accept_10_4_7_2_1_211 54 57 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 142 (accept_3_3 53 57 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 57 142 (Polychromatic418967fa.accept_7_3_1_2_1_247 52 57 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 51
  57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 142 (accept_3_3 50 57
  142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 142 (Polychromatic418967fa.accept_6_1_3_4_1_1
  49 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 57 142
  (Polychromatic418967fa.accept_7_6_1_2_1_230 48 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 57 142 (accept_3_3 47 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  57 142 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 57 142 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 57 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 142 (accept_3_3 44 57 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 57 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 57 142
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 57 142 (accept_3_3 41 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  57 142 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 57 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 57 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 142 (accept_3_3 38 57 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 57 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 57 142
  (Polychromatic418967fa.accept_14_8_1_2_1_965 36 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 57 142 (accept_3_3 35 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  57 142 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 57 142 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 57 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 142 (accept_3_3 32 57 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 57 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 57 142
  (Polychromatic418967fa.accept_12_6_9_10_1_565 30 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 57 142 (accept_3_3 29 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  57 142 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 57 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 57 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 142 (accept_3_3 26 57 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 57 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 57 142
  (Polychromatic418967fa.accept_7_3_1_2_1_247 24 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 57 142 (accept_3_3 23 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  57 142 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 57 142 (Polychromatic418967fa.accept_13_8_5_12_1_2755 21 57 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 142 (accept_3_3 20 57 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 57 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 57 142
  (Polychromatic418967fa.accept_12_6_9_10_1_565 18 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 57 142 (accept_3_3 17 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  57 142 (Polychromatic418967fa.accept_23_16_11_4_1_7328 16 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 57 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 57 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 142 (accept_3_3 14 57 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 57 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 57 142
  (Polychromatic418967fa.accept_11_1_2_10_1_1426 12 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 57 142 (accept_3_3 11 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  57 142 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 57 142 (Polychromatic418967fa.accept_10_9_7_2_1_887 9 57 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 142 (accept_3_3 8 57 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 57 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 142
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 142 (accept_3_3 5 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57
  142 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 57 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 57 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 57 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 142 (accept_3_3 2 57 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 57 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 57 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 142)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 142 (allA_of_3_1 56 56 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 55 142
  (allA_succ_of_accept 54 55 142 (Polychromatic418967fa.accept_13_2_3_12_1_735 54 55 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 142 (accept_3_3 53 55 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 55 142 (Polychromatic418967fa.accept_7_3_6_2_1_90 52 55 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 51
  55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 55 142 (accept_3_3 50 55
  142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 55 142 (Polychromatic418967fa.accept_4_1_3_2_1_3
  49 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 55 142
  (Polychromatic418967fa.accept_9_3_1_7_1_97 48 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 55 142 (accept_3_3 47 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  55 142 (Polychromatic418967fa.accept_7_4_6_2_1_451 46 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 55 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 55 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 55 142 (accept_3_3 44 55 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 142 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 55 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 142
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 142 (accept_3_3 41 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  55 142 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 55 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 55 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 55 142 (accept_3_3 38 55 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 55 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 55 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 142
  (Polychromatic418967fa.accept_7_1_6_2_1_18 36 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 55 142 (accept_3_3 35 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  55 142 (Polychromatic418967fa.accept_15_4_10_7_1_1356 34 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 55 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 55 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 142 (accept_3_3 32 55 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 55 142 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 55 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 55 142
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 55 142 (accept_3_3 29 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  55 142 (Polychromatic418967fa.accept_10_8_5_2_1_881 28 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 55 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 55 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 142 (accept_3_3 26 55 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 55 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 55 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 55 142
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 55 142 (accept_3_3 23 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  55 142 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 55 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 55 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 55 142 (accept_3_3 20 55 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 55 142 (Polychromatic418967fa.accept_15_4_10_7_1_1356 19 55 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 142
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 55 142 (accept_3_3 17 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  55 142 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 55 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 55 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 55 142 (accept_3_3 14 55 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 55 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 142
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 142 (accept_3_3 11 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  55 142 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 55 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 55 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 142 (accept_3_3 8 55 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 142 (Polychromatic418967fa.accept_10_7_5_2_1_880 7 55 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 142
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 55 142 (accept_3_3 5 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 55
  142 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 55 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 55 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 142 (accept_3_3 2 55 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 55 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 142)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 54 142 (allA_succ_of_accept 53 54 142 (accept_3_3 53 54 142 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 54 142 2 26 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 54 142 (Polychromatic418967fa.accept_12_3_6_10_1_576 51 54 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 54 142 2 25 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 54 142 (Polychromatic418967fa.accept_13_10_2_12_1_1332
  49 54 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 142 2 24 27 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 142 (accept_3_3 47
  54 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 54 142 2 23 27 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 54 142
  (Polychromatic418967fa.accept_7_3_5_2_1_17 45 54 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 54 142 2 22 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 54 142 (Polychromatic418967fa.accept_13_4_2_12_1_2800 43 54 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54 142 2 21 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 54 142 (accept_3_3 41 54 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 54 142 2 20 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 54 142 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 54 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 54 142 2 19 27 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 54 142
  (Polychromatic418967fa.accept_10_7_4_2_1_903 37 54 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 54 142 2 18 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 54 142 (accept_3_3 35 54 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 54
  142 2 17 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  54 142 (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 54 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 54 142 2 16 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 54 142 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 54 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 142 2 15 27 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 142 (accept_3_3 29 54 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 142 2 14 27 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 54 142
  (Polychromatic418967fa.accept_10_7_4_2_1_903 27 54 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 54 142 2 13 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 54 142 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 54 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54 142 2 12 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 54 142 (accept_3_3 23 54 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 54 142 2 11 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 54 142 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 54 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 54 142 2 10 27 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 54 142
  (Polychromatic418967fa.accept_13_6_2_12_1_2802 19 54 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 54 142 2 9 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 54 142 (accept_3_3 17 54 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54
  142 2 8 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  54 142 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 54 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 54 142 2 7 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 54 142 (Polychromatic418967fa.accept_15_13_9_7_1_2194 13 54 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 142 2 6 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 142 (accept_3_3 11 54 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 54 142 2 5 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 54 142 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 54 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 54 142 2 4 27 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 142
  (Polychromatic418967fa.accept_10_7_4_2_1_903 7 54 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 54 142 2 3 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 54 142 (accept_3_3 5 54 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 142
  2 2 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 54
  142 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 54 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 54 142 2 1 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 54 142 (Polychromatic418967fa.accept_13_1_2_12_1_1299 1 54 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 54 142)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53
  142 (allA_of_3_1 53 53 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 52 142 (allA_succ_of_accept 51 52 142
  (Polychromatic418967fa.accept_21_9_10_16_1_7327 51 52 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 52 142 2 25 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 52 142 (Polychromatic418967fa.accept_12_1_4_10_1_209 49 52 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 52 142 2 24 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 52 142 (accept_3_3 47 52 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 52 142 2 23 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 52 142 (Polychromatic418967fa.accept_21_3_10_16_1_4340 45 52
  142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 52 142 2 22 26 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 52 142
  (Polychromatic418967fa.accept_7_1_3_2_1_13 43 52 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 52 142 2 21 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 52 142 (accept_3_3 41 52 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 52
  142 2 20 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  52 142 (Polychromatic418967fa.accept_16_7_4_14_1_2860 39 52 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 52 142 2 19 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 52 142 (Polychromatic418967fa.accept_12_1_4_10_1_209 37 52 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 52 142 2 18 26 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 52 142 (accept_3_3 35 52 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 52 142 2 17 26 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 52 142
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 52 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 52 142 2 16 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 52 142 (Polychromatic418967fa.accept_11_9_8_10_1_934 31 52 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 52 142 2 15 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 52 142 (accept_3_3 29 52 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 52 142 2 14 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 52 142 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 52 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 52 142 2 13 26 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 52 142
  (Polychromatic418967fa.accept_12_1_4_10_1_209 25 52 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 52 142 2 12 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 52 142 (accept_3_3 23 52 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 52
  142 2 11 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  52 142 (Polychromatic418967fa.accept_23_21_6_4_1_7326 21 52 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 52 142 2 10 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 52 142 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 52 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 52 142 2 9 26 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 52 142 (accept_3_3 17 52 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 52 142 2 8 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 52 142 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 52 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 52 142 2 7 26 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 52 142
  (Polychromatic418967fa.accept_7_6_3_2_1_461 13 52 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 52 142 2 6 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 52 142 (accept_3_3 11 52 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 52
  142 2 5 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  52 142 (Polychromatic418967fa.accept_11_9_8_10_1_934 9 52 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 52 142 2 4 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 52 142 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 52 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 52 142 2 3 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 52 142 (accept_3_3 5 52 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 52 142 2 2 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 52 142 (Polychromatic418967fa.accept_17_3_1_6_1_251 3 52 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 52 142 2 1 26 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 52 142
  (Polychromatic418967fa.accept_7_1_3_2_1_13 1 52 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 52 142)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 142 (allA_succ_of_accept 50 51 142
  (accept_3_3 50 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 142
  (Polychromatic418967fa.accept_4_1_3_2_1_3 49 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 51 142 (Polychromatic418967fa.accept_9_3_6_7_1_562 48 51 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 142 (accept_3_3 47 51 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 51 142 (Polychromatic418967fa.accept_9_1_6_7_1_285 46 51 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 45
  51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 142 (accept_3_3 44 51
  142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 142 (Polychromatic418967fa.accept_6_1_3_4_1_1
  43 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 51 142
  (Polychromatic418967fa.accept_12_6_3_10_1_224 42 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 51 142 (accept_3_3 41 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  51 142 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 51 142 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 51 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 142 (accept_3_3 38 51 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 51 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 51 142
  (Polychromatic418967fa.accept_10_6_1_2_1_874 36 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 51 142 (accept_3_3 35 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  51 142 (Polychromatic418967fa.accept_19_15_13_9_1_7324 34 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 51 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 51 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 142 (accept_3_3 32 51 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 51 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 51 142
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 51 142 (accept_3_3 29 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  51 142 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 51 142 (Polychromatic418967fa.accept_15_12_6_7_1_1353 27 51 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 142 (accept_3_3 26 51 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 51 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 51 142
  (Polychromatic418967fa.accept_18_6_15_16_1_7325 24 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 51 142 (accept_3_3 23 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  51 142 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 51 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 51 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 142 (accept_3_3 20 51 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 51 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 51 142
  (Polychromatic418967fa.accept_12_6_3_10_1_224 18 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 51 142 (accept_3_3 17 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  51 142 (Polychromatic418967fa.accept_10_6_1_2_1_874 16 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 51 142 (Polychromatic418967fa.accept_19_15_13_9_1_7324 15 51 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 142 (accept_3_3 14 51 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 51 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 51 142
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 51 142 (accept_3_3 11 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  51 142 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 51 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 51 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 142 (accept_3_3 8 51 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 51 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51 142
  (Polychromatic418967fa.accept_10_6_1_2_1_874 6 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 142 (accept_3_3 5 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51
  142 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 51 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 51 142 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 51 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 142 (accept_3_3 2 51 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 51 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 51 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 142)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 142 (allA_of_3_1 50 50 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 49 142
  (allA_succ_of_accept 48 49 142 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 49 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 142 (accept_3_3 47 49 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 49 142 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 49 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 45
  49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 142 (accept_3_3 44 49
  142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 142 (Polychromatic418967fa.accept_4_3_1_2_1_62
  43 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 49 142
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 49 142 (accept_3_3 41 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  49 142 (Polychromatic418967fa.accept_12_4_1_10_1_221 40 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 49 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 49 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 142 (accept_3_3 38 49 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 49 142 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 49 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 142
  (Polychromatic418967fa.accept_16_4_1_14_1_3908 36 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 49 142 (accept_3_3 35 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  49 142 (Polychromatic418967fa.accept_13_8_10_12_1_1337 34 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 49 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 49 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 142 (accept_3_3 32 49 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 49 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 142
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 49 142 (accept_3_3 29 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  49 142 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 49 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 49 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 49 142 (accept_3_3 26 49 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 49 142 (Polychromatic418967fa.accept_15_10_4_7_1_3127 25 49 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 142
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 49 142 (accept_3_3 23 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  49 142 (Polychromatic418967fa.accept_13_9_10_12_1_2048 22 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 49 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 49 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 49 142 (accept_3_3 20 49 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 49 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 142
  (Polychromatic418967fa.accept_15_3_4_7_1_1352 18 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 49 142 (accept_3_3 17 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  49 142 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 49 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 49 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 49 142 (accept_3_3 14 49 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 49 142 (Polychromatic418967fa.accept_16_13_1_14_1_2855 13 49 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 142
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 49 142 (accept_3_3 11 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  49 142 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 49 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 49 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 142 (accept_3_3 8 49 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 49 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 49 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 49 142
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 49 142 (accept_3_3 5 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49
  142 (Polychromatic418967fa.accept_11_4_5_10_1_926 4 49 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 49 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 49 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 142 (accept_3_3 2 49 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 142 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 49 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 142)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 48 142 (allA_succ_of_accept 47 48 142 (accept_3_3 47 48 142 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 48 142 2 23 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 48 142 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 48 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 48 142 2 22 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 48 142 (Polychromatic418967fa.accept_7_1_6_2_1_18 43
  48 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 142 2 21 24 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 142 (accept_3_3 41
  48 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 48 142 2 20 24 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 48 142
  (Polychromatic418967fa.accept_7_4_6_2_1_451 39 48 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 48 142 2 19 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 48 142 (Polychromatic418967fa.accept_9_1_3_7_1_6 37 48 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 142 2 18 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 142 (accept_3_3 35 48 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48 142 2 17 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 48 142 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 48 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 48 142 2 16 24 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 48 142
  (Polychromatic418967fa.accept_7_3_6_2_1_90 31 48 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 48 142 2 15 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 48 142 (accept_3_3 29 48 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 48
  142 2 14 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  48 142 (Polychromatic418967fa.accept_11_5_4_10_1_524 27 48 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 48 142 2 13 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 48 142 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 48 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 142 2 12 24 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 142 (accept_3_3 23 48 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48 142 2 11 24 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 48 142
  (Polychromatic418967fa.accept_13_8_9_12_1_2813 21 48 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 48 142 2 10 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 48 142 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 48 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 142 2 9 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 142 (accept_3_3 17 48 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 48 142 2 8 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 48 142 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 48 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 48 142 2 7 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 142 (Polychromatic418967fa.accept_9_4_3_7_1_296 13
  48 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 142 2 6 24 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 142 (accept_3_3 11
  48 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48 142 2 5 24 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 48 142
  (Polychromatic418967fa.accept_18_9_12_16_1_7323 9 48 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 48 142 2 4 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 48 142 (Polychromatic418967fa.accept_17_7_14_6_1_4882 7 48 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 142 2 3 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 142 (accept_3_3 5 48 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 48 142 2 2 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 48 142 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 48 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 48 142 2 1 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 142 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 48
  142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48
  142)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 142 (allA_of_3_1 47 47 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 46 142 (allA_succ_of_accept 45 46 142 (Polychromatic418967fa.accept_11_1_2_10_1_1426
  45 46 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 46 142 2 22 23 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 46 142
  (Polychromatic418967fa.accept_13_4_7_12_1_2823 43 46 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 46 142 2 21 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 46 142 (accept_3_3 41 46 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 46
  142 2 20 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  46 142 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 46 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 46 142 2 19 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 46 142 (Polychromatic418967fa.accept_13_11_7_12_1_2758 37 46 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 46 142 2 18 23 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 46 142 (accept_3_3 35 46 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 46 142 2 17 23 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 46 142
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 46 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 46 142 2 16 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 46 142 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 46 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 46 142 2 15 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 46 142 (accept_3_3 29 46 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 46 142 2 14 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 46 142 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 46 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 46 142 2 13 23 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 46 142
  (Polychromatic418967fa.accept_15_10_1_7_1_5207 25 46 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 46 142 2 12 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 46 142 (accept_3_3 23 46 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 46
  142 2 11 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  46 142 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 46 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 46 142 2 10 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 46 142 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 46 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 46 142 2 9 23 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 46 142 (accept_3_3 17 46 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 46 142 2 8 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 46 142 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 46 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 46 142 2 7 23 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 46 142
  (Polychromatic418967fa.accept_7_6_4_2_1_236 13 46 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 46 142 2 6 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 46 142 (accept_3_3 11 46 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 46
  142 2 5 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  46 142 (Polychromatic418967fa.accept_14_9_4_2_1_983 9 46 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 46 142 2 4 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 46 142 (Polychromatic418967fa.accept_19_7_8_9_1_7322 7 46 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 46 142 2 3 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 46 142 (accept_3_3 5 46 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 46 142 2 2 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 46 142 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 46 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 46 142 2 1 23 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 46 142
  (Polychromatic418967fa.accept_10_1_6_2_1_867 1 46 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 46 142)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 142 (allA_succ_of_accept 44 45 142
  (accept_3_3 44 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 142
  (Polychromatic418967fa.accept_4_3_1_2_1_62 43 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 45 142 (Polychromatic418967fa.accept_11_9_1_10_1_920 42 45 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 142 (accept_3_3 41 45 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 45 142 (Polychromatic418967fa.accept_7_5_3_2_1_249 40 45 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 39
  45 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 142 (accept_3_3 38 45
  142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 142 (Polychromatic418967fa.accept_6_1_3_4_1_1
  37 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 142
  (Polychromatic418967fa.accept_7_1_3_2_1_13 36 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 45 142 (accept_3_3 35 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  45 142 (Polychromatic418967fa.accept_7_6_3_2_1_461 34 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 45 142 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 45 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 142 (accept_3_3 32 45 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 45 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 45 142
  (Polychromatic418967fa.accept_12_6_9_10_1_565 30 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 45 142 (accept_3_3 29 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  45 142 (Polychromatic418967fa.accept_10_8_5_2_1_881 28 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 45 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 45 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 142 (accept_3_3 26 45 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 45 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 45 142
  (Polychromatic418967fa.accept_11_2_1_10_1_196 24 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 45 142 (accept_3_3 23 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  45 142 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 45 142 (Polychromatic418967fa.accept_17_4_11_6_1_3730 21 45 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 142 (accept_3_3 20 45 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 45 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 45 142
  (Polychromatic418967fa.accept_10_8_5_2_1_881 18 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 45 142 (accept_3_3 17 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  45 142 (Polychromatic418967fa.accept_19_16_7_9_1_7321 16 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 45 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 45 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 142 (accept_3_3 14 45 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 45 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 45 142
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 45 142 (accept_3_3 11 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  45 142 (Polychromatic418967fa.accept_13_10_6_12_1_2780 10 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 45 142 (Polychromatic418967fa.accept_11_9_1_10_1_920 9 45 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 142 (accept_3_3 8 45 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 45 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 142
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 142 (accept_3_3 5 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45
  142 (Polychromatic418967fa.accept_17_4_11_6_1_3730 4 45 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 45 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 45 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 142 (accept_3_3 2 45 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 45 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 142)))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 44 142 (allA_of_3_1 44 44 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 43 142
  (allA_succ_of_accept 42 43 142 (Polychromatic418967fa.accept_13_3_4_12_1_36 42 43 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 43 142 (accept_3_3 41 43 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 43 142 (Polychromatic418967fa.accept_12_4_7_10_1_563 40 43 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 43 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 39
  43 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 142 (accept_3_3 38 43
  142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 142 (Polychromatic418967fa.accept_4_1_3_2_1_3
  37 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 142
  (Polychromatic418967fa.accept_14_8_1_2_1_965 36 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 142 (accept_3_3 35 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 142 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 43 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 142 (accept_3_3 32 43 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 142 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 43 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 142
  (Polychromatic418967fa.accept_20_10_3_2_1_4444 30 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 142 (accept_3_3 29 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 142 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 43 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 142 (accept_3_3 26 43 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 43 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 142
  (Polychromatic418967fa.accept_7_3_1_2_1_247 24 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 142 (accept_3_3 23 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 142 (Polychromatic418967fa.accept_14_8_1_2_1_965 22 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 43 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 142 (accept_3_3 20 43 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 142 (Polychromatic418967fa.accept_16_3_11_14_1_446 19 43 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 142
  (Polychromatic418967fa.accept_13_5_4_12_1_2058 18 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 142 (accept_3_3 17 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 142 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 43 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 142 (accept_3_3 14 43 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 43 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 142
  (Polychromatic418967fa.accept_19_12_5_9_1_7320 12 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 142 (accept_3_3 11 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 142 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 43 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 142 (accept_3_3 8 43 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 142 (Polychromatic418967fa.accept_13_7_4_12_1_1341 7 43 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 142
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 142 (accept_3_3 5 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  142 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 43 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 43 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 43 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 142 (accept_3_3 2 43 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 43 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 43 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 142)))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 42 142 (allA_succ_of_accept 41 42 142 (accept_3_3 41 42 142 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 42 142 2 20 21 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 42 142 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 42 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 42 142 2 19 21 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 42 142 (Polychromatic418967fa.accept_9_1_6_7_1_285 37
  42 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 142 2 18 21 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 142 (accept_3_3 35
  42 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 42 142 2 17 21 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 42 142
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 42 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 42 142 2 16 21 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 42 142 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 42 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 142 2 15 21 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 142 (accept_3_3 29 42 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 142 2 14 21 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 42 142 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 42 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 42 142 2 13 21 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 142
  (Polychromatic418967fa.accept_15_10_12_7_1_1358 25 42 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 42 142 2 12 21 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 42 142 (accept_3_3 23 42 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42
  142 2 11 21 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  42 142 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 42 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 42 142 2 10 21 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 42 142 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 42 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 142 2 9 21 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 142 (accept_3_3 17 42 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 42 142 2 8 21 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 42 142 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 42 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 42 142 2 7 21 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 142
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 42 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 42 142 2 6 21 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 42 142 (accept_3_3 11 42 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42
  142 2 5 21 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  42 142 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 42 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 42 142 2 4 21 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 42 142 (Polychromatic418967fa.accept_16_7_10_14_1_1884 7 42 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 142 2 3 21 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 142 (accept_3_3 5 42 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 42 142 2 2 21 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 42 142 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 42 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 42 142 2 1 21 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 142
  (Polychromatic418967fa.accept_9_1_6_7_1_285 1 42 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 42 142)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 142 (allA_of_3_1 41 41 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 40 142 (allA_succ_of_accept 39 40 142
  (Polychromatic418967fa.accept_7_4_5_2_1_243 39 40 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 40 142 2 19 20 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 40 142 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 40 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 40 142 2 18 20 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 40 142 (accept_3_3 35 40 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 40 142 2 17 20 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 40 142 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 40 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 40 142 2 16 20 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 40 142
  (Polychromatic418967fa.accept_7_3_5_2_1_17 31 40 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 40 142 2 15 20 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 40 142 (accept_3_3 29 40 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 40
  142 2 14 20 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  40 142 (Polychromatic418967fa.accept_15_12_10_7_1_1357 27 40 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 40 142 2 13 20 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 40 142 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 40 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 40 142 2 12 20 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 40 142 (accept_3_3 23 40 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 40 142 2 11 20 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 40 142
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 40 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 40 142 2 10 20 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 40 142 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 40 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 40 142 2 9 20 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 40 142 (accept_3_3 17 40 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 40 142 2 8 20 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 40 142 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 40 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 40 142 2 7 20 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 40 142 (Polychromatic418967fa.accept_12_1_4_10_1_209
  13 40 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 40 142 2 6 20 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 40 142 (accept_3_3 11
  40 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40 142 2 5 20 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 40 142
  (Polychromatic418967fa.accept_22_9_18_10_1_7319 9 40 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 40 142 2 4 20 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 40 142 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 40 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 40 142 2 3 20 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 40 142 (accept_3_3 5 40 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 40 142 2 2 20 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 40 142 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 40 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 40 142 2 1 20 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 40 142 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 40
  142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40
  142)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 142 (allA_succ_of_accept 38 39 142 (accept_3_3 38 39 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 37
  39 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 39 142
  (Polychromatic418967fa.accept_16_4_7_14_1_3897 36 39 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 39 142 (accept_3_3 35 39 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  39 142 (Polychromatic418967fa.accept_7_6_4_2_1_236 34 39 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 39 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 39 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 142 (accept_3_3 32 39 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 39 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 39 142
  (Polychromatic418967fa.accept_12_6_3_10_1_224 30 39 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 39 142 (accept_3_3 29 39 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  39 142 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 39 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 39 142 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 39 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 142 (accept_3_3 26 39 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 39 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 39 142
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 39 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 39 142 (accept_3_3 23 39 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  39 142 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 39 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 39 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 39 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 142 (accept_3_3 20 39 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 39 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 39 142
  (Polychromatic418967fa.accept_12_6_3_10_1_224 18 39 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 39 142 (accept_3_3 17 39 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  39 142 (Polychromatic418967fa.accept_11_5_6_10_1_1432 16 39 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 39 142 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 39 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 142 (accept_3_3 14 39 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 39 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 39 142
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 39 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 39 142 (accept_3_3 11 39 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  39 142 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 39 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 39 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 39 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 142 (accept_3_3 8 39 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 39 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39 142
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 39 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 142 (accept_3_3 5 39 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39
  142 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 39 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 39 142 (Polychromatic418967fa.accept_17_3_5_6_1_4826 3 39 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 142 (accept_3_3 2 39 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 39 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 39 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 142))))))))))))))))))))))))))))))))))))))) (allB_succ 38 142
  (allA_of_3_1 38 38 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 37 142 (allA_succ_of_accept 36 37 142
  (Polychromatic418967fa.accept_13_10_11_12_1_1320 36 37 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 37 142 (accept_3_3 35 37 142 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 37 142 (Polychromatic418967fa.accept_10_4_7_2_1_211 34 37 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 37 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 142 (accept_3_3 32 37 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 31
  37 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 142
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 37 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 142 (accept_3_3 29 37 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  37 142 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 37 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 37 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 142 (accept_3_3 26 37 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 142 (Polychromatic418967fa.accept_10_5_7_2_1_516 25 37 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 142
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 37 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 142 (accept_3_3 23 37 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 142 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 37 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 37 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 142 (accept_3_3 20 37 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 37 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 142
  (Polychromatic418967fa.accept_14_4_9_2_1_95 18 37 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 142 (accept_3_3 17 37 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  37 142 (Polychromatic418967fa.accept_11_5_4_10_1_524 16 37 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 37 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 142 (accept_3_3 14 37 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 142 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 37 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 142
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 37 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 142 (accept_3_3 11 37 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  37 142 (Polychromatic418967fa.accept_13_10_11_12_1_1320 10 37 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 37 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 142 (accept_3_3 8 37 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 37 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 142
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 37 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 142 (accept_3_3 5 37 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  142 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 37 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 37 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 142 (accept_3_3 2 37 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 142 (Polychromatic418967fa.accept_13_1_11_12_1_1322 1 37 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 142))))))))))))))))))))))))))))))))))))) (allB_succ 36 142
  (allA_succ_of_accept 35 36 142 (accept_3_3 35 36 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 36
  142 2 17 18 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  36 142 (Polychromatic418967fa.accept_13_7_10_12_1_2047 33 36 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 36 142 2 16 18 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 36 142 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 36 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 142 2 15 18 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 142 (accept_3_3 29 36 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 142 2 14 18 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 36 142
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 36 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 36 142 2 13 18 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 36 142 (Polychromatic418967fa.accept_16_9_4_14_1_1878 25 36 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 142 2 12 18 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 142 (accept_3_3 23 36 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36 142 2 11 18 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 36 142 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 36 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 36 142 2 10 18 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 142
  (Polychromatic418967fa.accept_13_6_10_12_1_2049 19 36 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 36 142 2 9 18 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 36 142 (accept_3_3 17 36 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36
  142 2 8 18 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  36 142 (Polychromatic418967fa.accept_13_2_10_12_1_757 15 36 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 36 142 2 7 18 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 36 142 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 36 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 142 2 6 18 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 142 (accept_3_3 11 36 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 36 142 2 5 18 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 36 142 (Polychromatic418967fa.accept_13_9_10_12_1_2048 9 36 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 36 142 2 4 18 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 36 142
  (Polychromatic418967fa.accept_11_7_3_10_1_1461 7 36 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 36 142 2 3 18 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 36 142 (accept_3_3 5 36 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 142
  2 2 18 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 36
  142 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 36 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 36 142 2 1 18 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 36 142 (Polychromatic418967fa.accept_10_1_6_2_1_867 1 36 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 36 142)))))))))))))))))))))))))))))))))))) (allB_succ 35 142 (allA_of_3_1 35
  35 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 34 142 (allA_succ_of_accept 33 34 142
  (Polychromatic418967fa.accept_13_7_8_12_1_2810 33 34 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 34 142 2 16 17 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 34 142 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 34 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 34 142 2 15 17 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 34 142 (accept_3_3 29 34 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 34 142 2 14 17 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 34 142 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 34 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 34 142 2 13 17 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 34 142
  (Polychromatic418967fa.accept_7_4_6_2_1_451 25 34 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 34 142 2 12 17 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 34 142 (accept_3_3 23 34 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 34
  142 2 11 17 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  34 142 (Polychromatic418967fa.accept_19_2_15_9_1_7318 21 34 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 34 142 2 10 17 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 34 142 (Polychromatic418967fa.accept_21_19_13_16_1_7317 19 34 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 34 142 2 9 17 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 34 142 (accept_3_3 17 34 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 34 142 2 8 17 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 34 142 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 34 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 34 142 2 7 17 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 34 142
  (Polychromatic418967fa.accept_11_2_1_10_1_196 13 34 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 34 142 2 6 17 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 34 142 (accept_3_3 11 34 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 34
  142 2 5 17 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  34 142 (Polychromatic418967fa.accept_11_9_1_10_1_920 9 34 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 34 142 2 4 17 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 34 142 (Polychromatic418967fa.accept_10_7_4_2_1_903 7 34 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 34 142 2 3 17 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 34 142 (accept_3_3 5 34 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 34 142 2 2 17 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 34 142 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 34 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 34 142 2 1 17 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 34 142
  (Polychromatic418967fa.accept_7_1_6_2_1_18 1 34 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 34 142)))))))))))))))))))))))))))))))))) (allB_succ 33 142 (allA_succ_of_accept 32 33 142 (accept_3_3 32 33
  142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 142 (Polychromatic418967fa.accept_4_3_1_2_1_62
  31 33 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 142
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 33 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 33 142 (accept_3_3 29 33 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  33 142 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 33 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 33 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 33 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 142 (accept_3_3 26 33 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 33 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 33 142
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 33 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 33 142 (accept_3_3 23 33 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  33 142 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 33 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 33 142 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 33 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 142 (accept_3_3 20 33 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 33 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 142
  (Polychromatic418967fa.accept_7_4_5_2_1_243 18 33 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 33 142 (accept_3_3 17 33 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  33 142 (Polychromatic418967fa.accept_19_16_14_9_1_7316 16 33 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 33 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 33 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 142 (accept_3_3 14 33 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 33 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 142
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 33 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 33 142 (accept_3_3 11 33 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  33 142 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 33 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 33 142 (Polychromatic418967fa.accept_17_9_16_6_1_4820 9 33 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 142 (accept_3_3 8 33 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 33 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 142
  (Polychromatic418967fa.accept_12_6_9_10_1_565 6 33 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 142 (accept_3_3 5 33 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33
  142 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 33 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 33 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 33 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 142 (accept_3_3 2 33 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 33 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 33 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 142))))))))))))))))))))))))))))))))) (allB_succ 32 142
  (allA_of_3_1 32 32 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 31 142 (allA_succ_of_accept 30 31 142
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 31 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 31 142 (accept_3_3 29 31 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  31 142 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 31 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 31 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 31 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 142 (accept_3_3 26 31 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 31 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 142
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 31 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 142 (accept_3_3 23 31 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  31 142 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 31 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 31 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 31 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 142 (accept_3_3 20 31 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 142 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 31 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 142
  (Polychromatic418967fa.accept_19_18_12_9_1_7315 18 31 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 142 (accept_3_3 17 31 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 142 (Polychromatic418967fa.accept_10_6_1_2_1_874 16 31 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 31 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 142 (accept_3_3 14 31 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 31 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 142
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 31 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 142 (accept_3_3 11 31 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 142 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 31 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 31 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 142 (accept_3_3 8 31 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 142 (Polychromatic418967fa.accept_13_7_5_12_1_1305 7 31 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 142
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 31 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 142 (accept_3_3 5 31 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  142 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 31 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 31 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 31 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 142 (accept_3_3 2 31 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 31 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 142))))))))))))))))))))))))))))))) (allB_succ 30 142
  (allA_succ_of_accept 29 30 142 (accept_3_3 29 30 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30
  142 2 14 15 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  30 142 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 30 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 30 142 2 13 15 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 30 142 (Polychromatic418967fa.accept_20_5_10_2_1_7314 25 30 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 142 2 12 15 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 142 (accept_3_3 23 30 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 142 2 11 15 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 30 142
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 30 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 30 142 2 10 15 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 30 142 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 30 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 142 2 9 15 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 142 (accept_3_3 17 30 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 30 142 2 8 15 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 30 142 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 30 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 30 142 2 7 15 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 142 (Polychromatic418967fa.accept_9_4_3_7_1_296 13
  30 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 142 2 6 15 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 142 (accept_3_3 11
  30 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 142 2 5 15 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 30 142
  (Polychromatic418967fa.accept_11_9_8_10_1_934 9 30 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 30 142 2 4 15 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 30 142 (Polychromatic418967fa.accept_13_7_4_12_1_1341 7 30 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 142 2 3 15 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 142 (accept_3_3 5 30 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 30 142 2 2 15 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 30 142 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 30 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 30 142 2 1 15 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 142 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 30
  142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 142))))))))))))))))))))))))))))))
  (allB_succ 29 142 (allA_of_3_1 29 29 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 28 142
  (allA_succ_of_accept 27 28 142 (Polychromatic418967fa.accept_11_5_6_10_1_1432 27 28 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 28 142 2 13 14 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 28 142 (Polychromatic418967fa.accept_10_5_8_2_1_517 25
  28 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 28 142 2 12 14 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 28 142 (accept_3_3 23
  28 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 28 142 2 11 14 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 28 142
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 28 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 28 142 2 10 14 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 28 142 (Polychromatic418967fa.accept_12_7_4_10_1_572 19 28 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 28 142 2 9 14 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 28 142 (accept_3_3 17 28 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 28 142 2 8 14 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 28 142 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 28 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 28 142 2 7 14 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 28 142 (Polychromatic418967fa.accept_9_4_1_7_1_293 13
  28 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 28 142 2 6 14 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 28 142 (accept_3_3 11
  28 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 28 142 2 5 14 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 28 142
  (Polychromatic418967fa.accept_15_9_13_7_1_1361 9 28 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 28 142 2 4 14 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 28 142 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 28 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 28 142 2 3 14 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 28 142 (accept_3_3 5 28 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 28 142 2 2 14 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 28 142 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 28 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 28 142 2 1 14 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 28 142 (Polychromatic418967fa.accept_12_1_4_10_1_209 1
  28 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 142))))))))))))))))))))))))))))
  (allB_succ 27 142 (allA_succ_of_accept 26 27 142 (accept_3_3 26 27 142 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 27 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 142 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 27 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 142 (accept_3_3 23 27 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 142 (Polychromatic418967fa.accept_7_1_6_2_1_18 22
  27 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 142
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 27 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 27 142 (accept_3_3 20 27 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  27 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 27 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 27 142 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 27 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 142 (accept_3_3 17 27 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 142 (Polychromatic418967fa.accept_17_16_10_6_1_7313 16 27 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 142
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 27 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 27 142 (accept_3_3 14 27 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  27 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 27 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 27 142 (Polychromatic418967fa.accept_17_12_10_6_1_3691 12 27 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 142 (accept_3_3 11 27 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 142 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 27 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 142
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 27 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 27 142 (accept_3_3 8 27 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27
  142 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 27 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 27 142 (Polychromatic418967fa.accept_11_6_5_10_1_2724 6 27 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 142 (accept_3_3 5 27 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 27 142 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 27 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 142 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 27
  142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 142 (accept_3_3 2 27 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 27
  142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 142)))))))))))))))))))))))))))
  (allB_succ 26 142 (allA_of_3_1 26 26 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 25 142
  (allA_succ_of_accept 24 25 142 (Polychromatic418967fa.accept_20_4_5_2_1_3119 24 25 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 142 (accept_3_3 23 25 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 25 142 (Polychromatic418967fa.accept_18_4_7_16_1_2307 22 25 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 142
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 25 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 25 142 (accept_3_3 20 25 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  25 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 25 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 25 142 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 25 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 142 (accept_3_3 17 25 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 25 142 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 25 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 25 142
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 25 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 25 142 (accept_3_3 14 25 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  25 142 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 25 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 25 142 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 25 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 142 (accept_3_3 11 25 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 25 142 (Polychromatic418967fa.accept_19_10_6_9_1_7312 10 25 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 25 142
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 25 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 25 142 (accept_3_3 8 25 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25
  142 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 25 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 25 142 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 25 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 25 142 (accept_3_3 5 25 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 25 142 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 25 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 25
  142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 142 (accept_3_3 2 25 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25 142 (Polychromatic418967fa.accept_15_1_10_7_1_4087
  1 25 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 142)))))))))))))))))))))))))
  (allB_succ 24 142 (allA_succ_of_accept 23 24 142 (accept_3_3 23 24 142 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 24 142 2 11 12 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 24 142 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 24 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 24 142 2 10 12 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 24 142 (Polychromatic418967fa.accept_7_5_3_2_1_249 19
  24 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 142 2 9 12 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 142 (accept_3_3 17
  24 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 24 142 2 8 12 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 24 142
  (Polychromatic418967fa.accept_7_1_3_2_1_13 15 24 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 24 142 2 7 12 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 24 142 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 24 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 142 2 6 12 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 142 (accept_3_3 11 24 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 24 142 2 5 12 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 24 142 (Polychromatic418967fa.accept_20_9_4_2_1_1900 9 24 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 24 142 2 4 12 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 24 142 (Polychromatic418967fa.accept_10_7_4_2_1_903 7
  24 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 142 2 3 12 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24 142 (accept_3_3 5 24
  142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 24 142 2 2 12 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 24 142
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 24 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 24 142 2 1 12 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 24 142 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 24 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 24 142)))))))))))))))))))))))) (allB_succ 23 142 (allA_of_3_1 23 23 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 22 142 (allA_succ_of_accept 21 22 142
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 22 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 22 142 2 10 11 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 22 142 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 22 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 22 142 2 9 11 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 22 142 (accept_3_3 17 22 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 22 142 2 8 11 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 22 142 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 22 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 22 142 2 7 11 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 22 142 (Polychromatic418967fa.accept_7_6_1_2_1_230 13
  22 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 22 142 2 6 11 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 22 142 (accept_3_3 11
  22 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 22 142 2 5 11 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 22 142
  (Polychromatic418967fa.accept_26_9_22_12_1_7311 9 22 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 22 142 2 4 11 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 22 142 (Polychromatic418967fa.accept_18_7_4_16_1_2299 7 22 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 22 142 2 3 11 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 22 142 (accept_3_3 5 22 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 22 142 2 2 11 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 22 142 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 22 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 22 142 2 1 11 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 22 142 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 22
  142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 142)))))))))))))))))))))) (allB_succ 21
  142 (allA_succ_of_accept 20 21 142 (accept_3_3 20 21 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 21 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 21 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 21 142 (Polychromatic418967fa.accept_12_6_9_10_1_565 18 21 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 142 (accept_3_3 17 21 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 142 (Polychromatic418967fa.accept_10_6_1_2_1_874 16 21 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 142
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 21 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 21 142 (accept_3_3 14 21 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  21 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 21 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 21 142 (Polychromatic418967fa.accept_14_12_7_2_1_1663 12 21 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 142 (accept_3_3 11 21 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 142 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 21 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 142
  (Polychromatic418967fa.accept_10_9_1_2_1_522 9 21 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 21 142 (accept_3_3 8 21 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21
  142 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 21 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 21 142 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 21 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 142 (accept_3_3 5 21 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 21 142 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 21 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 21
  142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 142 (accept_3_3 2 21 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 21
  142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 142))))))))))))))))))))) (allB_succ 20
  142 (allA_of_3_1 20 20 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 19 142 (allA_succ_of_accept 18 19 142
  (Polychromatic418967fa.accept_7_4_5_2_1_243 18 19 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 142 (accept_3_3 17 19 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 142 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 19 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 19 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 142 (accept_3_3 14 19 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 19 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 142
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 19 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 142 (accept_3_3 11 19 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 142 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 19 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 19 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 142 (accept_3_3 8 19 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 142 (Polychromatic418967fa.accept_10_7_9_2_1_1887 7 19 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 142
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 19 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 142 (accept_3_3 5 19 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  142 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 19 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 19 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 142 (accept_3_3 2 19 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 19 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 142))))))))))))))))))) (allB_succ 18 142 (allA_succ_of_accept 17
  18 142 (accept_3_3 17 18 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 142 2 8 9 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 18 142
  (Polychromatic418967fa.accept_10_5_8_2_1_517 15 18 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 18 142 2 7 9 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 18 142 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 18 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 142 2 6 9 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 142 (accept_3_3 11 18 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 18 142 2 5 9 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 18 142 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 18 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 142 2 4 9 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 142 (Polychromatic418967fa.accept_13_7_5_12_1_1305 7
  18 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 142 2 3 9 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 142 (accept_3_3 5 18
  142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 142 2 2 9 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18 142
  (Polychromatic418967fa.accept_11_3_7_10_1_180 3 18 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 18 142 2 1 9 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 18 142 (Polychromatic418967fa.accept_13_1_5_12_1_306 1 18 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 18 142)))))))))))))))))) (allB_succ 17 142 (allA_of_3_1 17 17 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 16 142 (allA_succ_of_accept 15 16 142
  (Polychromatic418967fa.accept_11_4_5_10_1_926 15 16 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 16 142 2 7 8 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 16 142 (Polychromatic418967fa.accept_12_1_4_10_1_209 13 16 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 16 142 2 6 8 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 16 142 (accept_3_3 11 16 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 16 142 2 5 8 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 16 142 (Polychromatic418967fa.accept_13_9_3_12_1_2025 9 16 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 16 142 2 4 8 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 16 142 (Polychromatic418967fa.accept_12_7_4_10_1_572 7
  16 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 16 142 2 3 8 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 16 142 (accept_3_3 5 16
  142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 16 142 2 2 8 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 16 142
  (Polychromatic418967fa.accept_22_3_16_10_1_7310 3 16 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 16 142 2 1 8 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 16 142 (Polychromatic418967fa.accept_10_1_6_2_1_867 1 16 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 16 142)))))))))))))))) (allB_succ 15 142 (allA_succ_of_accept 14 15 142
  (accept_3_3 14 15 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 142
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 15 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 15 142 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 15 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 142 (accept_3_3 11 15 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 15 142 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 15 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 15
  142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 142 (accept_3_3 8 15 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 15
  142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 142
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 15 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 142 (accept_3_3 5 15 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15
  142 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 15 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 15 142 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 15 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 142 (accept_3_3 2 15 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 15 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 15 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 142))))))))))))))) (allB_succ 14 142 (allA_of_3_1 14 14 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 142 (allA_succ_of_accept 12 13 142
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 13 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 142 (accept_3_3 11 13 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 142 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 13 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 13 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 142 (accept_3_3 8 13 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 13 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 142
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 13 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 142 (accept_3_3 5 13 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  142 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 13 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 13 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 142 (accept_3_3 2 13 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 142 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 13 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 142))))))))))))) (allB_succ 12 142 (allA_succ_of_accept 11 12
  142 (accept_3_3 11 12 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 12 142 2 5 6 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 12 142
  (Polychromatic418967fa.accept_11_9_1_10_1_920 9 12 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 12 142 2 4 6 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 12 142 (Polychromatic418967fa.accept_14_7_12_2_1_2502 7 12 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 142 2 3 6 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 142 (accept_3_3 5 12 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 12 142 2 2 6 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 12 142 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 12 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 142 2 1 6 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 142 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 12
  142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 142)))))))))))) (allB_succ 11 142
  (allA_of_3_1 11 11 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 10 142 (allA_succ_of_accept 9 10 142
  (Polychromatic418967fa.accept_13_9_10_12_1_2048 9 10 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 10 142 2 4 5 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 10 142 (Polychromatic418967fa.accept_13_7_10_12_1_2047 7 10 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 10 142 2 3 5 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 10 142 (accept_3_3 5 10 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 10 142 2 2 5 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 10 142 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 10 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 10 142 2 1 5 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 10 142 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 10
  142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 142)))))))))) (allB_succ 9 142
  (allA_succ_of_accept 8 9 142 (accept_3_3 8 9 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 142
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 9 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 9 142 (Polychromatic418967fa.accept_12_6_9_10_1_565 6 9 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 142 (accept_3_3 5 9 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 9 142 (Polychromatic418967fa.accept_14_4_9_2_1_95 4 9 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 142 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 9
  142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 142 (accept_3_3 2 9 142
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 142 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 9
  142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 142))))))))) (allB_succ 8 142
  (allA_of_3_1 8 8 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 7 142 (allA_succ_of_accept 6 7 142
  (Polychromatic418967fa.accept_13_6_7_12_1_3504 6 7 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 142 (accept_3_3 5 7 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 142
  (Polychromatic418967fa.accept_10_4_7_2_1_211 4 7 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 142 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 7 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 142 (accept_3_3 2 7 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 7 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 142))))))) (allB_succ 6 142 (allA_succ_of_accept 5 6 142
  (accept_3_3 5 6 142 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 142 2 2 3 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 142
  (Polychromatic418967fa.accept_7_3_6_2_1_90 3 6 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 6 142 2 1 3 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 142 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 6 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 6 142)))))) (allB_succ 5 142 (allA_of_3_1 5 5 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 4 142 (allA_succ_of_accept 3 4 142 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 4 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 4 142 2 1 2 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 4 142
  (Polychromatic418967fa.accept_9_1_4_7_1_7 1 4 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 142)))) (allB_succ 3 142 (allA_succ_of_accept 2 3 142 (accept_3_3 2 3 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 142 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 3 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 142))) (allB_succ 2 142 (allA_of_3_1 2 2 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  142))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


